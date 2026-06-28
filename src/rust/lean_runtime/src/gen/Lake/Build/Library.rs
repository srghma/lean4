// Lean compiler output
// Module: Lake.Build.Library
// Imports: Lake.Config.FacetConfig Lake.Build.Common Lake.Build.Targets Lake.Build.Job.Register Lake.Build.Target.Fetch Lake.Build.Infos Lake.Util.Proc
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_Pos_prevn;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_ReaderT_instMonad___redArg};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_normalize,
};
use crate::r#gen::Init::System::IO::l_instMonadBaseIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::System::Platform::{l_System_Platform_isOSX, l_System_Platform_isWindows};
use crate::r#gen::Lake::Build::Actions::l_Lake_compileStaticLib;
use crate::r#gen::Lake::Build::Common::{
    initialize_Lake_Build_Common, l_Lake_buildArtifactUnlessUpToDate, l_Lake_buildLeanSharedLib,
    runtime_initialize_Lake_Build_Common,
};
use crate::r#gen::Lake::Build::Data::{
    l_Lake_instDataKindDynlib, l_Lake_instDataKindFilePath, l_Lake_instDataKindUnit,
};
use crate::r#gen::Lake::Build::Facets::{
    l_Lake_ExternLib_dynlibFacet, l_Lake_LeanLib_defaultFacet, l_Lake_LeanLib_extraDepFacet,
    l_Lake_LeanLib_leanArtsFacet, l_Lake_LeanLib_sharedFacet, l_Lake_LeanLib_staticExportFacet,
    l_Lake_LeanLib_staticFacet, l_Lake_Module_leanArtsFacet, l_Lake_Package_extraDepFacet,
};
use crate::r#gen::Lake::Build::Fetch::l_Lake_ModuleFacet_fetch___redArg;
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, l_Lake_LeanLib_modulesFacet, l_Lake_Module_importsFacet,
    l_Lake_Module_transImportsFacet, runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_Job_toOpaque___redArg;
use crate::r#gen::Lake::Build::Job::Monad::{
    l_Lake_Job_await___redArg, l_Lake_Job_collectArray___redArg, l_Lake_Job_mapM___redArg,
    l_Lake_Job_mix___redArg, l_Lake_Job_mixArray___redArg,
};
use crate::r#gen::Lake::Build::Job::Register::{
    initialize_Lake_Build_Job_Register, l_Lake_Job_renew___redArg, l_Lake_ensureJob___redArg,
    runtime_initialize_Lake_Build_Job_Register,
};
use crate::r#gen::Lake::Build::Key::l_Lake_PartialBuildKey_toString;
use crate::r#gen::Lake::Build::Target::Fetch::{
    initialize_Lake_Build_Target_Fetch,
    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux,
    l_Lake_Target_fetchIn___redArg, runtime_initialize_Lake_Build_Target_Fetch,
};
use crate::r#gen::Lake::Build::Targets::{
    initialize_Lake_Build_Targets, l_Lake_Package_fetchTargetJob,
    runtime_initialize_Lake_Build_Targets,
};
use crate::r#gen::Lake::Build::Trace::l_Lake_BuildTrace_nil;
use crate::r#gen::Lake::Config::FacetConfig::{
    initialize_Lake_Config_FacetConfig, runtime_initialize_Lake_Config_FacetConfig,
};
use crate::r#gen::Lake::Config::Kinds::{
    l_Lake_ExternLib_keyword, l_Lake_Module_keyword, l_Lake_Package_keyword,
};
use crate::r#gen::Lake::Config::LeanLib::{l_Lake_LeanLib_isPlugin, l_Lake_LeanLib_libName};
use crate::r#gen::Lake::Config::Module::l_Lake_LeanLib_getModuleArray;
use crate::r#gen::Lake::Util::EStateT::{
    l_Lake_EStateT_instFunctor___redArg, l_Lake_EStateT_instMonad___redArg___lam__1,
    l_Lake_EStateT_instMonad___redArg___lam__3, l_Lake_EStateT_instMonad___redArg___lam__5,
    l_Lake_EStateT_instMonad___redArg___lam__9, l_Lake_EStateT_instPure___redArg___lam__0,
};
use crate::r#gen::Lake::Util::EquipT::l_Lake_EquipT_instMonad___redArg;
use crate::r#gen::Lake::Util::FilePath::{l_Lake_joinRelative, l_Lake_mkRelPathString};
use crate::r#gen::Lake::Util::IO::l_Lake_createParentDirs;
use crate::r#gen::Lake::Util::Log::l_Lake_instDecidableEqVerbosity;
use crate::r#gen::Lake::Util::NativeLib::{l_Lake_nameToSharedLib, l_Lake_nameToStaticLib};
use crate::r#gen::Lake::Util::Proc::{
    initialize_Lake_Util_Proc, l_Lake_proc, runtime_initialize_Lake_Util_Proc,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::lean_imports_rs::Init::Core::lean_task_pure;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_string_utf8_byte_size, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_prim_handle_mk, lean_io_prim_handle_put_str, lean_io_wait,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_7, lean_box, lean_box_usize, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0: u64 = 0;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 110, 105, 108, 62, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [58, 32, 115, 111, 109, 101, 32, 109, 111, 100, 117, 108, 101, 115, 32, 104, 97, 118, 101, 32, 98, 97, 100, 32, 105, 109, 112, 111, 114, 116, 115, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0_value
) as *mut LeanObject;
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__1_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0],
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__1_value
        ) as *mut LeanObject,
        12295998048739818339 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__4_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 8) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__3_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__0_value
        ) as *mut LeanObject,
        256 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__4_value
) as *mut LeanObject;
pub static mut l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__4_value
)
    as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0_value:
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
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0_value
) as *mut LeanObject;
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanLib_leanArtsFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_leanArtsFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_leanArtsFacetConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanLib_leanArtsFacetConfig___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_leanArtsFacetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_leanArtsFacetConfig___closed__1_value) as *mut LeanObject;
static mut l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_leanArtsFacetConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanLib_leanArtsFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [102, 105, 108, 101, 108, 105, 115, 116, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [65793 as *mut LeanObject] };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 105, 98, 116, 111, 111, 108, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [45, 115, 116, 97, 116, 105, 99, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 111, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [45, 102, 105, 108, 101, 108, 105, 115, 116, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5_value
) as *mut LeanObject;
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 98, 106, 115, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 120, 112, 111, 114, 116, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [58, 115, 116, 97, 116, 105, 99, 0],
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        32, 40, 119, 105, 116, 104, 111, 117, 116, 32, 101, 120, 112, 111, 114, 116, 115, 41, 0,
    ],
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        32, 40, 119, 105, 116, 104, 32, 101, 120, 112, 111, 114, 116, 115, 41, 0,
    ],
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2_value
) as *mut LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [39, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1_value) as *mut LeanObject;
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [39, 44, 32, 103, 111, 116, 32, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3_value) as *mut LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4_value) as *mut LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [117, 110, 107, 110, 111, 119, 110, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5_value) as *mut LeanObject;
pub static l_Lake_LeanLib_staticFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLib_staticFacetConfig___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_staticFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticFacetConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanLib_staticFacetConfig___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_staticFacetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticFacetConfig___closed__1_value) as *mut LeanObject;
static mut l_Lake_LeanLib_staticFacetConfig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_staticFacetConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanLib_staticFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanLib_staticExportFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_staticExportFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticExportFacetConfig___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_LeanLib_staticExportFacetConfig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_staticExportFacetConfig___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanLib_staticExportFacetConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0_value) as *mut LeanObject;
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [58, 115, 104, 97, 114, 101, 100, 0],
};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0_value
) as *mut LeanObject;
pub static l_Lake_LeanLib_sharedFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_sharedFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_sharedFacetConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanLib_sharedFacetConfig___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_sharedFacetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_sharedFacetConfig___closed__1_value) as *mut LeanObject;
static mut l_Lake_LeanLib_sharedFacetConfig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_sharedFacetConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanLib_sharedFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [58, 101, 120, 116, 114, 97, 68, 101, 112, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1_value
) as *mut LeanObject;
pub static l_Lake_LeanLib_extraDepFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_extraDepFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_extraDepFacetConfig___closed__0_value) as *mut LeanObject;
static mut l_Lake_LeanLib_extraDepFacetConfig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_extraDepFacetConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanLib_extraDepFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [60, 99, 111, 108, 108, 101, 99, 116, 105, 111, 110, 62, 0]};
static mut l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0_value
) as *mut LeanObject;
pub static l_Lake_LeanLib_defaultFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLib_defaultFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_defaultFacetConfig___closed__0_value) as *mut LeanObject;
static mut l_Lake_LeanLib_defaultFacetConfig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_defaultFacetConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanLib_defaultFacetConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanLib_initFacetConfigs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_initFacetConfigs___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanLib_initFacetConfigs___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_initFacetConfigs___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanLib_initFacetConfigs___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_initFacetConfigs___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanLib_initFacetConfigs___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_initFacetConfigs___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanLib_initFacetConfigs___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_initFacetConfigs___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanLib_initFacetConfigs___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_initFacetConfigs___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanLib_initFacetConfigs___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanLib_initFacetConfigs___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanLib_initFacetConfigs: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_initLibraryFacetConfigs: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(
    mut v_a_3851_: *mut LeanObject,
    mut v_x_3852_: *mut LeanObject,
) -> u8 {
    let mut v___x_3853_: u8 = 0;
    let mut v_key_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3852_) == 0 {
                    v___x_3853_ = 0;
                    return v___x_3853_;
                } else {
                    v_key_3854_ = lean_ctor_get(v_x_3852_, 0);
                    v_tail_3855_ = lean_ctor_get(v_x_3852_, 2);
                    v_name_3856_ = lean_ctor_get(v_key_3854_, 1);
                    v_name_3857_ = lean_ctor_get(v_a_3851_, 1);
                    v___x_3858_ = lean_name_eq(v_name_3856_, v_name_3857_);
                    if v___x_3858_ == 0 {
                        v_x_3852_ = v_tail_3855_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3858_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg___boxed(
    mut v_a_3860_: *mut LeanObject,
    mut v_x_3861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3862_: u8 = 0;
    let mut v_r_3863_: *mut LeanObject = core::ptr::null_mut();
    v_res_3862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_3860_, v_x_3861_);
    lean_dec(v_x_3861_);
    lean_dec_ref(v_a_3860_);
    v_r_3863_ = lean_box((v_res_3862_) as usize);
    return v_r_3863_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u64 = 0;
    v___x_3864_ = lean_unsigned_to_nat(1723);
    v___x_3865_ = lean_uint64_of_nat(v___x_3864_);
    return v___x_3865_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_x_3866_: *mut LeanObject,
    mut v_x_3867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3873_: u8 = 0;
    let mut v_name_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3877_: u64 = 0;
    let mut v___x_3878_: u64 = 0;
    let mut v___x_3879_: u64 = 0;
    let mut v_fold_3880_: u64 = 0;
    let mut v___x_3881_: u64 = 0;
    let mut v___x_3882_: u64 = 0;
    let mut v___x_3883_: u64 = 0;
    let mut v___x_3884_: usize = 0;
    let mut v___x_3885_: usize = 0;
    let mut v___x_3886_: usize = 0;
    let mut v___x_3887_: usize = 0;
    let mut v___x_3888_: usize = 0;
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: u64 = 0;
    let mut v_hash_3896_: u64 = 0;
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3867_) == 0 {
                    return v_x_3866_;
                } else {
                    v_key_3868_ = lean_ctor_get(v_x_3867_, 0);
                    v_value_3869_ = lean_ctor_get(v_x_3867_, 1);
                    v_tail_3870_ = lean_ctor_get(v_x_3867_, 2);
                    v_isSharedCheck_3897_ = (!lean_is_exclusive(v_x_3867_)) as u8;
                    if v_isSharedCheck_3897_ == 0 {
                        v___x_3872_ = v_x_3867_;
                        v_isShared_3873_ = v_isSharedCheck_3897_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3870_);
                        lean_inc(v_value_3869_);
                        lean_inc(v_key_3868_);
                        lean_dec(v_x_3867_);
                        v___x_3872_ = lean_box(0);
                        v_isShared_3873_ = v_isSharedCheck_3897_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_3874_ = lean_ctor_get(v_key_3868_, 1);
                v___x_3875_ = lean_array_get_size(v_x_3866_);
                if lean_obj_tag(v_name_3874_) == 0 {
                    v___x_3895_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_3877_ = v___x_3895_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3896_ = lean_ctor_get_uint64(
                        v_name_3874_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3877_ = v_hash_3896_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3878_ = 32u64;
                v___x_3879_ = lean_uint64_shift_right(v___y_3877_, v___x_3878_);
                v_fold_3880_ = lean_uint64_xor(v___y_3877_, v___x_3879_);
                v___x_3881_ = 16u64;
                v___x_3882_ = lean_uint64_shift_right(v_fold_3880_, v___x_3881_);
                v___x_3883_ = lean_uint64_xor(v_fold_3880_, v___x_3882_);
                v___x_3884_ = lean_uint64_to_usize(v___x_3883_);
                v___x_3885_ = lean_usize_of_nat(v___x_3875_);
                v___x_3886_ = 1usize;
                v___x_3887_ = lean_usize_sub(v___x_3885_, v___x_3886_);
                v___x_3888_ = lean_usize_land(v___x_3884_, v___x_3887_);
                v___x_3889_ = lean_array_uget_borrowed(v_x_3866_, v___x_3888_);
                lean_inc(v___x_3889_);
                if v_isShared_3873_ == 0 {
                    lean_ctor_set(v___x_3872_, 2, v___x_3889_);
                    v___x_3891_ = v___x_3872_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_key_3868_);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_value_3869_);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 2, v___x_3889_);
                    v___x_3891_ = v_reuseFailAlloc_3894_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3892_ = lean_array_uset(v_x_3866_, v___x_3888_, v___x_3891_);
                v_x_3866_ = v___x_3892_;
                v_x_3867_ = v_tail_3870_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(
    mut v_i_3898_: *mut LeanObject,
    mut v_source_3899_: *mut LeanObject,
    mut v_target_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    let mut v_es_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3901_ = lean_array_get_size(v_source_3899_);
                v___x_3902_ = lean_nat_dec_lt(v_i_3898_, v___x_3901_);
                if v___x_3902_ == 0 {
                    lean_dec_ref(v_source_3899_);
                    lean_dec(v_i_3898_);
                    return v_target_3900_;
                } else {
                    v_es_3903_ = lean_array_fget(v_source_3899_, v_i_3898_);
                    v___x_3904_ = lean_box(0);
                    v_source_3905_ = lean_array_fset(v_source_3899_, v_i_3898_, v___x_3904_);
                    v_target_3906_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3900_, v_es_3903_);
                    v___x_3907_ = lean_unsigned_to_nat(1);
                    v___x_3908_ = lean_nat_add(v_i_3898_, v___x_3907_);
                    lean_dec(v_i_3898_);
                    v_i_3898_ = v___x_3908_;
                    v_source_3899_ = v_source_3905_;
                    v_target_3900_ = v_target_3906_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(
    mut v_data_3910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    v___x_3911_ = lean_array_get_size(v_data_3910_);
    v___x_3912_ = lean_unsigned_to_nat(2);
    v_nbuckets_3913_ = lean_nat_mul(v___x_3911_, v___x_3912_);
    v___x_3914_ = lean_unsigned_to_nat(0);
    v___x_3915_ = lean_box(0);
    v___x_3916_ = lean_mk_array(v_nbuckets_3913_, v___x_3915_);
    v___x_3917_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v___x_3914_, v_data_3910_, v___x_3916_);
    return v___x_3917_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(
    mut v_m_3918_: *mut LeanObject,
    mut v_a_3919_: *mut LeanObject,
    mut v_b_3920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3926_: u64 = 0;
    let mut v___x_3927_: u64 = 0;
    let mut v___x_3928_: u64 = 0;
    let mut v_fold_3929_: u64 = 0;
    let mut v___x_3930_: u64 = 0;
    let mut v___x_3931_: u64 = 0;
    let mut v___x_3932_: u64 = 0;
    let mut v___x_3933_: usize = 0;
    let mut v___x_3934_: usize = 0;
    let mut v___x_3935_: usize = 0;
    let mut v___x_3936_: usize = 0;
    let mut v___x_3937_: usize = 0;
    let mut v_bkt_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: u8 = 0;
    let mut v_val_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut v_unused_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: u64 = 0;
    let mut v_hash_3964_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3921_ = lean_ctor_get(v_m_3918_, 0);
                v_buckets_3922_ = lean_ctor_get(v_m_3918_, 1);
                v_name_3923_ = lean_ctor_get(v_a_3919_, 1);
                v___x_3924_ = lean_array_get_size(v_buckets_3922_);
                if lean_obj_tag(v_name_3923_) == 0 {
                    v___x_3963_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_3926_ = v___x_3963_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3964_ = lean_ctor_get_uint64(
                        v_name_3923_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3926_ = v_hash_3964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3927_ = 32u64;
                v___x_3928_ = lean_uint64_shift_right(v___y_3926_, v___x_3927_);
                v_fold_3929_ = lean_uint64_xor(v___y_3926_, v___x_3928_);
                v___x_3930_ = 16u64;
                v___x_3931_ = lean_uint64_shift_right(v_fold_3929_, v___x_3930_);
                v___x_3932_ = lean_uint64_xor(v_fold_3929_, v___x_3931_);
                v___x_3933_ = lean_uint64_to_usize(v___x_3932_);
                v___x_3934_ = lean_usize_of_nat(v___x_3924_);
                v___x_3935_ = 1usize;
                v___x_3936_ = lean_usize_sub(v___x_3934_, v___x_3935_);
                v___x_3937_ = lean_usize_land(v___x_3933_, v___x_3936_);
                v_bkt_3938_ = lean_array_uget_borrowed(v_buckets_3922_, v___x_3937_);
                v___x_3939_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_3919_, v_bkt_3938_);
                if v___x_3939_ == 0 {
                    lean_inc_ref(v_buckets_3922_);
                    lean_inc(v_size_3921_);
                    v_isSharedCheck_3960_ = (!lean_is_exclusive(v_m_3918_)) as u8;
                    if v_isSharedCheck_3960_ == 0 {
                        v_unused_3961_ = lean_ctor_get(v_m_3918_, 1);
                        lean_dec(v_unused_3961_);
                        v_unused_3962_ = lean_ctor_get(v_m_3918_, 0);
                        lean_dec(v_unused_3962_);
                        v___x_3941_ = v_m_3918_;
                        v_isShared_3942_ = v_isSharedCheck_3960_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_3918_);
                        v___x_3941_ = lean_box(0);
                        v_isShared_3942_ = v_isSharedCheck_3960_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_3920_);
                    lean_dec_ref(v_a_3919_);
                    return v_m_3918_;
                }
            }
            2 => {
                v___x_3943_ = lean_unsigned_to_nat(1);
                v_size_x27_3944_ = lean_nat_add(v_size_3921_, v___x_3943_);
                lean_dec(v_size_3921_);
                lean_inc(v_bkt_3938_);
                v___x_3945_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3945_, 0, v_a_3919_);
                lean_ctor_set(v___x_3945_, 1, v_b_3920_);
                lean_ctor_set(v___x_3945_, 2, v_bkt_3938_);
                v_buckets_x27_3946_ = lean_array_uset(v_buckets_3922_, v___x_3937_, v___x_3945_);
                v___x_3947_ = lean_unsigned_to_nat(4);
                v___x_3948_ = lean_nat_mul(v_size_x27_3944_, v___x_3947_);
                v___x_3949_ = lean_unsigned_to_nat(3);
                v___x_3950_ = lean_nat_div(v___x_3948_, v___x_3949_);
                lean_dec(v___x_3948_);
                v___x_3951_ = lean_array_get_size(v_buckets_x27_3946_);
                v___x_3952_ = lean_nat_dec_le(v___x_3950_, v___x_3951_);
                lean_dec(v___x_3950_);
                if v___x_3952_ == 0 {
                    v_val_3953_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_buckets_x27_3946_);
                    if v_isShared_3942_ == 0 {
                        lean_ctor_set(v___x_3941_, 1, v_val_3953_);
                        lean_ctor_set(v___x_3941_, 0, v_size_x27_3944_);
                        v___x_3955_ = v___x_3941_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_size_x27_3944_);
                        lean_ctor_set(v_reuseFailAlloc_3956_, 1, v_val_3953_);
                        v___x_3955_ = v_reuseFailAlloc_3956_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3942_ == 0 {
                        lean_ctor_set(v___x_3941_, 1, v_buckets_x27_3946_);
                        lean_ctor_set(v___x_3941_, 0, v_size_x27_3944_);
                        v___x_3958_ = v___x_3941_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_size_x27_3944_);
                        lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_buckets_x27_3946_);
                        v___x_3958_ = v_reuseFailAlloc_3959_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3955_;
            }
            4 => {
                return v___x_3958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(
    mut v_m_3965_: *mut LeanObject,
    mut v_a_3966_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3971_: u64 = 0;
    let mut v___x_3972_: u64 = 0;
    let mut v___x_3973_: u64 = 0;
    let mut v_fold_3974_: u64 = 0;
    let mut v___x_3975_: u64 = 0;
    let mut v___x_3976_: u64 = 0;
    let mut v___x_3977_: u64 = 0;
    let mut v___x_3978_: usize = 0;
    let mut v___x_3979_: usize = 0;
    let mut v___x_3980_: usize = 0;
    let mut v___x_3981_: usize = 0;
    let mut v___x_3982_: usize = 0;
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: u64 = 0;
    let mut v_hash_3986_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3967_ = lean_ctor_get(v_m_3965_, 1);
                v_name_3968_ = lean_ctor_get(v_a_3966_, 1);
                v___x_3969_ = lean_array_get_size(v_buckets_3967_);
                if lean_obj_tag(v_name_3968_) == 0 {
                    v___x_3985_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_3971_ = v___x_3985_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3986_ = lean_ctor_get_uint64(
                        v_name_3968_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3971_ = v_hash_3986_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3972_ = 32u64;
                v___x_3973_ = lean_uint64_shift_right(v___y_3971_, v___x_3972_);
                v_fold_3974_ = lean_uint64_xor(v___y_3971_, v___x_3973_);
                v___x_3975_ = 16u64;
                v___x_3976_ = lean_uint64_shift_right(v_fold_3974_, v___x_3975_);
                v___x_3977_ = lean_uint64_xor(v_fold_3974_, v___x_3976_);
                v___x_3978_ = lean_uint64_to_usize(v___x_3977_);
                v___x_3979_ = lean_usize_of_nat(v___x_3969_);
                v___x_3980_ = 1usize;
                v___x_3981_ = lean_usize_sub(v___x_3979_, v___x_3980_);
                v___x_3982_ = lean_usize_land(v___x_3978_, v___x_3981_);
                v___x_3983_ = lean_array_uget_borrowed(v_buckets_3967_, v___x_3982_);
                v___x_3984_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_3966_, v___x_3983_);
                return v___x_3984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(
    mut v_m_3987_: *mut LeanObject,
    mut v_a_3988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3989_: u8 = 0;
    let mut v_r_3990_: *mut LeanObject = core::ptr::null_mut();
    v_res_3989_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_3987_, v_a_3988_);
    lean_dec_ref(v_a_3988_);
    lean_dec_ref(v_m_3987_);
    v_r_3990_ = lean_box((v_res_3989_) as usize);
    return v_r_3990_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(
    mut v_self_3991_: *mut LeanObject,
    mut v_root_3992_: *mut LeanObject,
    mut v_col_3993_: *mut LeanObject,
    mut v_a_3994_: *mut LeanObject,
    mut v_a_3995_: *mut LeanObject,
    mut v_a_3996_: *mut LeanObject,
    mut v_a_3997_: *mut LeanObject,
    mut v_a_3998_: *mut LeanObject,
    mut v_a_3999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_col_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mods_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modSet_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasErrors_4007_: u8 = 0;
    let mut v___x_4008_: u8 = 0;
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4011_: u8 = 0;
    let mut v_lib_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_task_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_col_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4030_: usize = 0;
    let mut v___x_4031_: usize = 0;
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mods_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modSet_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasErrors_4037_: u8 = 0;
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4040_: u8 = 0;
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut v_reuseFailAlloc_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut v_unused_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut v_unused_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mods_4005_ = lean_ctor_get(v_col_3993_, 0);
                v_modSet_4006_ = lean_ctor_get(v_col_3993_, 1);
                v_hasErrors_4007_ = lean_ctor_get_uint8(
                    v_col_3993_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v___x_4008_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_modSet_4006_, v_root_3992_);
                if v___x_4008_ == 0 {
                    lean_inc_ref(v_modSet_4006_);
                    lean_inc_ref(v_mods_4005_);
                    v_isSharedCheck_4069_ = (!lean_is_exclusive(v_col_3993_)) as u8;
                    if v_isSharedCheck_4069_ == 0 {
                        v_unused_4070_ = lean_ctor_get(v_col_3993_, 1);
                        lean_dec(v_unused_4070_);
                        v_unused_4071_ = lean_ctor_get(v_col_3993_, 0);
                        lean_dec(v_unused_4071_);
                        v___x_4010_ = v_col_3993_;
                        v_isShared_4011_ = v_isSharedCheck_4069_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_col_3993_);
                        v___x_4010_ = lean_box(0);
                        v_isShared_4011_ = v_isSharedCheck_4069_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_3994_);
                    lean_dec_ref(v_root_3992_);
                    v_col_4002_ = v_col_3993_;
                    v___y_4003_ = v_a_3999_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4004_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4004_, 0, v_col_4002_);
                lean_ctor_set(v___x_4004_, 1, v___y_4003_);
                return v___x_4004_;
            }
            2 => {
                v_lib_4012_ = lean_ctor_get(v_root_3992_, 0);
                v_pkg_4013_ = lean_ctor_get(v_lib_4012_, 0);
                v_name_4014_ = lean_ctor_get(v_root_3992_, 1);
                v_keyName_4015_ = lean_ctor_get(v_pkg_4013_, 2);
                v___x_4016_ = lean_box(0);
                lean_inc_ref_n(v_root_3992_, 2);
                v___x_4017_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_4006_, v_root_3992_, v___x_4016_);
                v___x_4018_ = l_Lake_Module_importsFacet;
                lean_inc(v_name_4014_);
                lean_inc(v_keyName_4015_);
                v___x_4019_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4019_, 0, v_keyName_4015_);
                lean_ctor_set(v___x_4019_, 1, v_name_4014_);
                v___x_4020_ = l_Lake_Module_keyword;
                v___x_4021_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_4021_, 0, v___x_4019_);
                lean_ctor_set(v___x_4021_, 1, v___x_4020_);
                lean_ctor_set(v___x_4021_, 2, v_root_3992_);
                lean_ctor_set(v___x_4021_, 3, v___x_4018_);
                lean_inc_ref(v_a_3994_);
                lean_inc_ref(v_a_3998_);
                lean_inc(v_a_3997_);
                lean_inc(v_a_3996_);
                lean_inc(v_a_3995_);
                v___x_4022_ = lean_apply_7(
                    v_a_3994_,
                    v___x_4021_,
                    v_a_3995_,
                    v_a_3996_,
                    v_a_3997_,
                    v_a_3998_,
                    v_a_3999_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4022_) == 0 {
                    v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
                    lean_inc(v_a_4023_);
                    v_a_4024_ = lean_ctor_get(v___x_4022_, 1);
                    lean_inc(v_a_4024_);
                    lean_dec_ref_known(v___x_4022_, 2);
                    v_task_4025_ = lean_ctor_get(v_a_4023_, 0);
                    lean_inc_ref(v_task_4025_);
                    lean_dec(v_a_4023_);
                    v___x_4026_ = lean_io_wait(v_task_4025_);
                    if lean_obj_tag(v___x_4026_) == 0 {
                        v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
                        lean_inc(v_a_4027_);
                        lean_dec_ref_known(v___x_4026_, 2);
                        if v_isShared_4011_ == 0 {
                            lean_ctor_set(v___x_4010_, 1, v___x_4017_);
                            v_col_4029_ = v___x_4010_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 2, (1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_mods_4005_);
                            lean_ctor_set(v_reuseFailAlloc_4046_, 1, v___x_4017_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_4046_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                v_hasErrors_4007_,
                            );
                            v_col_4029_ = v_reuseFailAlloc_4046_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_3994_);
                        lean_dec_ref(v_root_3992_);
                        v_isSharedCheck_4057_ = (!lean_is_exclusive(v___x_4026_)) as u8;
                        if v_isSharedCheck_4057_ == 0 {
                            v_unused_4058_ = lean_ctor_get(v___x_4026_, 1);
                            lean_dec(v_unused_4058_);
                            v_unused_4059_ = lean_ctor_get(v___x_4026_, 0);
                            lean_dec(v_unused_4059_);
                            v___x_4048_ = v___x_4026_;
                            v_isShared_4049_ = v_isSharedCheck_4057_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v___x_4026_);
                            v___x_4048_ = lean_box(0);
                            v_isShared_4049_ = v_isSharedCheck_4057_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_4017_);
                    lean_del_object(v___x_4010_);
                    lean_dec_ref(v_mods_4005_);
                    lean_dec_ref(v_a_3994_);
                    lean_dec_ref(v_root_3992_);
                    v_a_4060_ = lean_ctor_get(v___x_4022_, 0);
                    v_a_4061_ = lean_ctor_get(v___x_4022_, 1);
                    v_isSharedCheck_4068_ = (!lean_is_exclusive(v___x_4022_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v___x_4063_ = v___x_4022_;
                        v_isShared_4064_ = v_isSharedCheck_4068_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4061_);
                        lean_inc(v_a_4060_);
                        lean_dec(v___x_4022_);
                        v___x_4063_ = lean_box(0);
                        v_isShared_4064_ = v_isSharedCheck_4068_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v_sz_4030_ = lean_array_size(v_a_4027_);
                v___x_4031_ = 0usize;
                v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_3991_, v_a_4027_, v_sz_4030_, v___x_4031_, v_col_4029_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_4024_);
                lean_dec(v_a_4027_);
                if lean_obj_tag(v___x_4032_) == 0 {
                    v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
                    lean_inc(v_a_4033_);
                    v_a_4034_ = lean_ctor_get(v___x_4032_, 1);
                    lean_inc(v_a_4034_);
                    lean_dec_ref_known(v___x_4032_, 2);
                    v_mods_4035_ = lean_ctor_get(v_a_4033_, 0);
                    v_modSet_4036_ = lean_ctor_get(v_a_4033_, 1);
                    v_hasErrors_4037_ = lean_ctor_get_uint8(
                        v_a_4033_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_isSharedCheck_4045_ = (!lean_is_exclusive(v_a_4033_)) as u8;
                    if v_isSharedCheck_4045_ == 0 {
                        v___x_4039_ = v_a_4033_;
                        v_isShared_4040_ = v_isSharedCheck_4045_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_modSet_4036_);
                        lean_inc(v_mods_4035_);
                        lean_dec(v_a_4033_);
                        v___x_4039_ = lean_box(0);
                        v_isShared_4040_ = v_isSharedCheck_4045_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_root_3992_);
                    return v___x_4032_;
                }
            }
            4 => {
                v___x_4041_ = lean_array_push(v_mods_4035_, v_root_3992_);
                if v_isShared_4040_ == 0 {
                    lean_ctor_set(v___x_4039_, 0, v___x_4041_);
                    v___x_4043_ = v___x_4039_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4041_);
                    lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_modSet_4036_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4044_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_hasErrors_4037_,
                    );
                    v___x_4043_ = v_reuseFailAlloc_4044_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_col_4002_ = v___x_4043_;
                v___y_4003_ = v_a_4034_;
                state = 1;
                continue;
            }
            6 => {
                v___x_4050_ = 1;
                if v_isShared_4011_ == 0 {
                    lean_ctor_set(v___x_4010_, 1, v___x_4017_);
                    v___x_4052_ = v___x_4010_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_mods_4005_);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_4017_);
                    v___x_4052_ = v_reuseFailAlloc_4056_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_4052_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_4050_,
                );
                if v_isShared_4049_ == 0 {
                    lean_ctor_set_tag(v___x_4048_, 0);
                    lean_ctor_set(v___x_4048_, 1, v_a_4024_);
                    lean_ctor_set(v___x_4048_, 0, v___x_4052_);
                    v___x_4054_ = v___x_4048_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
                    lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_a_4024_);
                    v___x_4054_ = v_reuseFailAlloc_4055_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4054_;
            }
            9 => {
                if v_isShared_4064_ == 0 {
                    v___x_4066_ = v___x_4063_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4060_);
                    lean_ctor_set(v_reuseFailAlloc_4067_, 1, v_a_4061_);
                    v___x_4066_ = v_reuseFailAlloc_4067_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(
    mut v_self_4072_: *mut LeanObject,
    mut v_as_4073_: *mut LeanObject,
    mut v_sz_4074_: usize,
    mut v_i_4075_: usize,
    mut v_b_4076_: *mut LeanObject,
    mut v___y_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
    mut v___y_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: usize = 0;
    let mut v___x_4088_: usize = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4090_ = lean_usize_dec_lt(v_i_4075_, v_sz_4074_);
                if v___x_4090_ == 0 {
                    lean_dec_ref(v___y_4077_);
                    v___x_4091_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4091_, 0, v_b_4076_);
                    lean_ctor_set(v___x_4091_, 1, v___y_4082_);
                    return v___x_4091_;
                } else {
                    v_a_4092_ = lean_array_uget_borrowed(v_as_4073_, v_i_4075_);
                    v_lib_4093_ = lean_ctor_get(v_a_4092_, 0);
                    v_name_4094_ = lean_ctor_get(v_lib_4093_, 1);
                    v_name_4095_ = lean_ctor_get(v_self_4072_, 1);
                    v___x_4096_ = lean_name_eq(v_name_4094_, v_name_4095_);
                    if v___x_4096_ == 0 {
                        v_a_4085_ = v_b_4076_;
                        v_a_4086_ = v___y_4082_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v___y_4077_);
                        lean_inc(v_a_4092_);
                        v___x_4097_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_4072_, v_a_4092_, v_b_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
                        if lean_obj_tag(v___x_4097_) == 0 {
                            v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
                            lean_inc(v_a_4098_);
                            v_a_4099_ = lean_ctor_get(v___x_4097_, 1);
                            lean_inc(v_a_4099_);
                            lean_dec_ref_known(v___x_4097_, 2);
                            v_a_4085_ = v_a_4098_;
                            v_a_4086_ = v_a_4099_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v___y_4077_);
                            return v___x_4097_;
                        }
                    }
                }
            }
            1 => {
                v___x_4087_ = 1usize;
                v___x_4088_ = lean_usize_add(v_i_4075_, v___x_4087_);
                v_i_4075_ = v___x_4088_;
                v_b_4076_ = v_a_4085_;
                v___y_4082_ = v_a_4086_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(
    mut v_self_4100_: *mut LeanObject,
    mut v_as_4101_: *mut LeanObject,
    mut v_sz_4102_: *mut LeanObject,
    mut v_i_4103_: *mut LeanObject,
    mut v_b_4104_: *mut LeanObject,
    mut v___y_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4112_: usize = 0;
    let mut v_i_boxed_4113_: usize = 0;
    let mut v_res_4114_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4112_ = lean_unbox_usize(v_sz_4102_);
    lean_dec(v_sz_4102_);
    v_i_boxed_4113_ = lean_unbox_usize(v_i_4103_);
    lean_dec(v_i_4103_);
    v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_4100_, v_as_4101_, v_sz_boxed_4112_, v_i_boxed_4113_, v_b_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    lean_dec_ref(v___y_4109_);
    lean_dec(v___y_4108_);
    lean_dec(v___y_4107_);
    lean_dec(v___y_4106_);
    lean_dec_ref(v_as_4101_);
    lean_dec_ref(v_self_4100_);
    return v_res_4114_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(
    mut v_self_4115_: *mut LeanObject,
    mut v_root_4116_: *mut LeanObject,
    mut v_col_4117_: *mut LeanObject,
    mut v_a_4118_: *mut LeanObject,
    mut v_a_4119_: *mut LeanObject,
    mut v_a_4120_: *mut LeanObject,
    mut v_a_4121_: *mut LeanObject,
    mut v_a_4122_: *mut LeanObject,
    mut v_a_4123_: *mut LeanObject,
    mut v_a_4124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4125_: *mut LeanObject = core::ptr::null_mut();
    v_res_4125_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(
        v_self_4115_,
        v_root_4116_,
        v_col_4117_,
        v_a_4118_,
        v_a_4119_,
        v_a_4120_,
        v_a_4121_,
        v_a_4122_,
        v_a_4123_,
    );
    lean_dec_ref(v_a_4122_);
    lean_dec(v_a_4121_);
    lean_dec(v_a_4120_);
    lean_dec(v_a_4119_);
    lean_dec_ref(v_self_4115_);
    return v_res_4125_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(
    mut v_00_u03b2_4126_: *mut LeanObject,
    mut v_m_4127_: *mut LeanObject,
    mut v_a_4128_: *mut LeanObject,
) -> u8 {
    let mut v___x_4129_: u8 = 0;
    v___x_4129_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_4127_, v_a_4128_);
    return v___x_4129_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(
    mut v_00_u03b2_4130_: *mut LeanObject,
    mut v_m_4131_: *mut LeanObject,
    mut v_a_4132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4133_: u8 = 0;
    let mut v_r_4134_: *mut LeanObject = core::ptr::null_mut();
    v_res_4133_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_4130_, v_m_4131_, v_a_4132_);
    lean_dec_ref(v_a_4132_);
    lean_dec_ref(v_m_4131_);
    v_r_4134_ = lean_box((v_res_4133_) as usize);
    return v_r_4134_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(
    mut v_00_u03b2_4135_: *mut LeanObject,
    mut v_m_4136_: *mut LeanObject,
    mut v_a_4137_: *mut LeanObject,
    mut v_b_4138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    v___x_4139_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_m_4136_, v_a_4137_, v_b_4138_);
    return v___x_4139_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(
    mut v_00_u03b2_4140_: *mut LeanObject,
    mut v_a_4141_: *mut LeanObject,
    mut v_x_4142_: *mut LeanObject,
) -> u8 {
    let mut v___x_4143_: u8 = 0;
    v___x_4143_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_4141_, v_x_4142_);
    return v___x_4143_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_4144_: *mut LeanObject,
    mut v_a_4145_: *mut LeanObject,
    mut v_x_4146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4147_: u8 = 0;
    let mut v_r_4148_: *mut LeanObject = core::ptr::null_mut();
    v_res_4147_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_4144_, v_a_4145_, v_x_4146_);
    lean_dec(v_x_4146_);
    lean_dec_ref(v_a_4145_);
    v_r_4148_ = lean_box((v_res_4147_) as usize);
    return v_r_4148_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(
    mut v_00_u03b2_4149_: *mut LeanObject,
    mut v_data_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    v___x_4151_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_data_4150_);
    return v___x_4151_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(
    mut v_00_u03b2_4152_: *mut LeanObject,
    mut v_i_4153_: *mut LeanObject,
    mut v_source_4154_: *mut LeanObject,
    mut v_target_4155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    v___x_4156_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v_i_4153_, v_source_4154_, v_target_4155_);
    return v___x_4156_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_4157_: *mut LeanObject,
    mut v_x_4158_: *mut LeanObject,
    mut v_x_4159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_4158_, v_x_4159_);
    return v___x_4160_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(
    mut v_self_4161_: *mut LeanObject,
    mut v_as_4162_: *mut LeanObject,
    mut v_sz_4163_: usize,
    mut v_i_4164_: usize,
    mut v_b_4165_: *mut LeanObject,
    mut v___y_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: usize = 0;
    let mut v___x_4180_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4173_ = lean_usize_dec_lt(v_i_4164_, v_sz_4163_);
                if v___x_4173_ == 0 {
                    lean_dec_ref(v___y_4166_);
                    v___x_4174_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4174_, 0, v_b_4165_);
                    lean_ctor_set(v___x_4174_, 1, v___y_4171_);
                    return v___x_4174_;
                } else {
                    v_a_4175_ = lean_array_uget_borrowed(v_as_4162_, v_i_4164_);
                    lean_inc_ref(v___y_4166_);
                    lean_inc(v_a_4175_);
                    v___x_4176_ =
                        l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(
                            v_self_4161_,
                            v_a_4175_,
                            v_b_4165_,
                            v___y_4166_,
                            v___y_4167_,
                            v___y_4168_,
                            v___y_4169_,
                            v___y_4170_,
                            v___y_4171_,
                        );
                    if lean_obj_tag(v___x_4176_) == 0 {
                        v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
                        lean_inc(v_a_4177_);
                        v_a_4178_ = lean_ctor_get(v___x_4176_, 1);
                        lean_inc(v_a_4178_);
                        lean_dec_ref_known(v___x_4176_, 2);
                        v___x_4179_ = 1usize;
                        v___x_4180_ = lean_usize_add(v_i_4164_, v___x_4179_);
                        v_i_4164_ = v___x_4180_;
                        v_b_4165_ = v_a_4177_;
                        v___y_4171_ = v_a_4178_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_4166_);
                        return v___x_4176_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(
    mut v_self_4182_: *mut LeanObject,
    mut v_as_4183_: *mut LeanObject,
    mut v_sz_4184_: *mut LeanObject,
    mut v_i_4185_: *mut LeanObject,
    mut v_b_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
    mut v___y_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4194_: usize = 0;
    let mut v_i_boxed_4195_: usize = 0;
    let mut v_res_4196_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4194_ = lean_unbox_usize(v_sz_4184_);
    lean_dec(v_sz_4184_);
    v_i_boxed_4195_ = lean_unbox_usize(v_i_4185_);
    lean_dec(v_i_4185_);
    v_res_4196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_4182_, v_as_4183_, v_sz_boxed_4194_, v_i_boxed_4195_, v_b_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
    lean_dec_ref(v___y_4191_);
    lean_dec(v___y_4190_);
    lean_dec(v___y_4189_);
    lean_dec(v___y_4188_);
    lean_dec_ref(v_as_4183_);
    lean_dec_ref(v_self_4182_);
    return v_res_4196_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    v___x_4199_ =
        l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1;
    v___x_4200_ = l_Lake_BuildTrace_nil(v___x_4199_);
    return v___x_4200_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(
    mut v_self_4202_: *mut LeanObject,
    mut v_col_4203_: *mut LeanObject,
    mut v___x_4204_: *mut LeanObject,
    mut v___x_4205_: u8,
    mut v___x_4206_: *mut LeanObject,
    mut v___y_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
    mut v___y_4209_: *mut LeanObject,
    mut v___y_4210_: *mut LeanObject,
    mut v___y_4211_: *mut LeanObject,
    mut v___y_4212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4216_: usize = 0;
    let mut v___x_4217_: usize = 0;
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4223_: u8 = 0;
    let mut v_mods_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasErrors_4225_: u8 = 0;
    let mut v___y_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v_a_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4251_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4255_: u8 = 0;
    let mut v_a_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_self_4202_);
                v___x_4214_ = l_Lake_LeanLib_getModuleArray(v_self_4202_);
                if lean_obj_tag(v___x_4214_) == 0 {
                    v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
                    lean_inc(v_a_4215_);
                    lean_dec_ref_known(v___x_4214_, 1);
                    v_sz_4216_ = lean_array_size(v_a_4215_);
                    v___x_4217_ = 0usize;
                    v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_4202_, v_a_4215_, v_sz_4216_, v___x_4217_, v_col_4203_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
                    lean_dec(v_a_4215_);
                    if lean_obj_tag(v___x_4218_) == 0 {
                        v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
                        v_a_4220_ = lean_ctor_get(v___x_4218_, 1);
                        v_isSharedCheck_4246_ = (!lean_is_exclusive(v___x_4218_)) as u8;
                        if v_isSharedCheck_4246_ == 0 {
                            v___x_4222_ = v___x_4218_;
                            v_isShared_4223_ = v_isSharedCheck_4246_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4220_);
                            lean_inc(v_a_4219_);
                            lean_dec(v___x_4218_);
                            v___x_4222_ = lean_box(0);
                            v_isShared_4223_ = v_isSharedCheck_4246_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4206_);
                        lean_dec(v___x_4204_);
                        lean_dec_ref(v_self_4202_);
                        v_a_4247_ = lean_ctor_get(v___x_4218_, 0);
                        v_a_4248_ = lean_ctor_get(v___x_4218_, 1);
                        v_isSharedCheck_4255_ = (!lean_is_exclusive(v___x_4218_)) as u8;
                        if v_isSharedCheck_4255_ == 0 {
                            v___x_4250_ = v___x_4218_;
                            v_isShared_4251_ = v_isSharedCheck_4255_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4248_);
                            lean_inc(v_a_4247_);
                            lean_dec(v___x_4218_);
                            v___x_4250_ = lean_box(0);
                            v_isShared_4251_ = v_isSharedCheck_4255_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_4207_);
                    lean_dec(v___x_4206_);
                    lean_dec(v___x_4204_);
                    lean_dec_ref(v_col_4203_);
                    lean_dec_ref(v_self_4202_);
                    v_a_4256_ = lean_ctor_get(v___x_4214_, 0);
                    lean_inc(v_a_4256_);
                    lean_dec_ref_known(v___x_4214_, 1);
                    v___x_4257_ = lean_io_error_to_string(v_a_4256_);
                    v___x_4258_ = 3;
                    v___x_4259_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_4259_, 0, v___x_4257_);
                    lean_ctor_set_uint8(
                        v___x_4259_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_4258_,
                    );
                    v___x_4260_ = lean_array_get_size(v___y_4212_);
                    v___x_4261_ = lean_array_push(v___y_4212_, v___x_4259_);
                    v___x_4262_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4262_, 0, v___x_4260_);
                    lean_ctor_set(v___x_4262_, 1, v___x_4261_);
                    return v___x_4262_;
                }
            }
            1 => {
                v_mods_4224_ = lean_ctor_get(v_a_4219_, 0);
                lean_inc_ref(v_mods_4224_);
                v_hasErrors_4225_ = lean_ctor_get_uint8(
                    v_a_4219_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                lean_dec(v_a_4219_);
                if v_hasErrors_4225_ == 0 {
                    lean_dec_ref(v_self_4202_);
                    v___y_4227_ = v_a_4220_;
                    state = 2;
                    continue;
                } else {
                    v_name_4239_ = lean_ctor_get(v_self_4202_, 1);
                    lean_inc(v_name_4239_);
                    lean_dec_ref(v_self_4202_);
                    v___x_4240_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_4239_,
                        v_hasErrors_4225_,
                    );
                    v___x_4241_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3;
                    v___x_4242_ = lean_string_append(v___x_4240_, v___x_4241_);
                    v___x_4243_ = 3;
                    v___x_4244_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_4244_, 0, v___x_4242_);
                    lean_ctor_set_uint8(
                        v___x_4244_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_4243_,
                    );
                    v___x_4245_ = lean_array_push(v_a_4220_, v___x_4244_);
                    v___y_4227_ = v___x_4245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4228_ = lean_mk_empty_array_with_capacity(v___x_4204_);
                v___x_4229_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0;
                v___x_4230_ = 0;
                v___x_4231_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once), _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
                v___x_4232_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_4232_, 0, v___x_4228_);
                lean_ctor_set(v___x_4232_, 1, v___x_4231_);
                lean_ctor_set(v___x_4232_, 2, v___x_4204_);
                lean_ctor_set_uint8(
                    v___x_4232_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4230_,
                );
                lean_ctor_set_uint8(
                    v___x_4232_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_4205_,
                );
                if v_isShared_4223_ == 0 {
                    lean_ctor_set(v___x_4222_, 1, v___x_4232_);
                    lean_ctor_set(v___x_4222_, 0, v_mods_4224_);
                    v___x_4234_ = v___x_4222_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_mods_4224_);
                    lean_ctor_set(v_reuseFailAlloc_4238_, 1, v___x_4232_);
                    v___x_4234_ = v_reuseFailAlloc_4238_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4235_ = lean_task_pure(v___x_4234_);
                v___x_4236_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_4236_, 0, v___x_4235_);
                lean_ctor_set(v___x_4236_, 1, v___x_4206_);
                lean_ctor_set(v___x_4236_, 2, v___x_4229_);
                lean_ctor_set_uint8(
                    v___x_4236_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4205_,
                );
                v___x_4237_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4237_, 0, v___x_4236_);
                lean_ctor_set(v___x_4237_, 1, v___y_4227_);
                return v___x_4237_;
            }
            4 => {
                if v_isShared_4251_ == 0 {
                    v___x_4253_ = v___x_4250_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4247_);
                    lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_a_4248_);
                    v___x_4253_ = v_reuseFailAlloc_4254_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(
    mut v_self_4263_: *mut LeanObject,
    mut v_col_4264_: *mut LeanObject,
    mut v___x_4265_: *mut LeanObject,
    mut v___x_4266_: *mut LeanObject,
    mut v___x_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
    mut v___y_4271_: *mut LeanObject,
    mut v___y_4272_: *mut LeanObject,
    mut v___y_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7761__boxed_4275_: u8 = 0;
    let mut v_res_4276_: *mut LeanObject = core::ptr::null_mut();
    v___x_7761__boxed_4275_ = (lean_unbox(v___x_4266_) as u8);
    v_res_4276_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(
        v_self_4263_,
        v_col_4264_,
        v___x_4265_,
        v___x_7761__boxed_4275_,
        v___x_4267_,
        v___y_4268_,
        v___y_4269_,
        v___y_4270_,
        v___y_4271_,
        v___y_4272_,
        v___y_4273_,
    );
    lean_dec_ref(v___y_4272_);
    lean_dec(v___y_4271_);
    lean_dec(v___y_4270_);
    lean_dec(v___y_4269_);
    return v_res_4276_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1()
-> *mut LeanObject {
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    v___x_4279_ = lean_box(0);
    v___x_4280_ = lean_unsigned_to_nat(16);
    v___x_4281_ = lean_mk_array(v___x_4280_, v___x_4279_);
    return v___x_4281_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2()
-> *mut LeanObject {
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    v___x_4282_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once
        ),
        _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1,
    );
    v___x_4283_ = lean_unsigned_to_nat(0);
    v___x_4284_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4284_, 0, v___x_4283_);
    lean_ctor_set(v___x_4284_, 1, v___x_4282_);
    return v___x_4284_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3()
-> *mut LeanObject {
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_col_4288_: *mut LeanObject = core::ptr::null_mut();
    v___x_4285_ = 0;
    v___x_4286_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once
        ),
        _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2,
    );
    v___x_4287_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0;
    v_col_4288_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v_col_4288_, 0, v___x_4287_);
    lean_ctor_set(v_col_4288_, 1, v___x_4286_);
    lean_ctor_set_uint8(
        v_col_4288_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_4285_,
    );
    return v_col_4288_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(
    mut v_self_4289_: *mut LeanObject,
    mut v_a_4290_: *mut LeanObject,
    mut v_a_4291_: *mut LeanObject,
    mut v_a_4292_: *mut LeanObject,
    mut v_a_4293_: *mut LeanObject,
    mut v_a_4294_: *mut LeanObject,
    mut v_a_4295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: u8 = 0;
    let mut v_col_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    v___x_4297_ = lean_box(0);
    v___x_4298_ = lean_unsigned_to_nat(0);
    v___x_4299_ = 0;
    v_col_4300_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once
        ),
        _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3,
    );
    v___x_4301_ = lean_box((v___x_4299_) as usize);
    v___f_4302_ = lean_alloc_closure(
        l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        5,
    );
    lean_closure_set(v___f_4302_, 0, v_self_4289_);
    lean_closure_set(v___f_4302_, 1, v_col_4300_);
    lean_closure_set(v___f_4302_, 2, v___x_4298_);
    lean_closure_set(v___f_4302_, 3, v___x_4301_);
    lean_closure_set(v___f_4302_, 4, v___x_4297_);
    v___x_4303_ = l_Lake_ensureJob___redArg(
        v___x_4297_,
        v___f_4302_,
        v_a_4290_,
        v_a_4291_,
        v_a_4292_,
        v_a_4293_,
        v_a_4294_,
        v_a_4295_,
    );
    return v___x_4303_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(
    mut v_self_4304_: *mut LeanObject,
    mut v_a_4305_: *mut LeanObject,
    mut v_a_4306_: *mut LeanObject,
    mut v_a_4307_: *mut LeanObject,
    mut v_a_4308_: *mut LeanObject,
    mut v_a_4309_: *mut LeanObject,
    mut v_a_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4312_: *mut LeanObject = core::ptr::null_mut();
    v_res_4312_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(
        v_self_4304_,
        v_a_4305_,
        v_a_4306_,
        v_a_4307_,
        v_a_4308_,
        v_a_4309_,
        v_a_4310_,
    );
    lean_dec_ref(v_a_4309_);
    lean_dec(v_a_4308_);
    lean_dec(v_a_4307_);
    lean_dec(v_a_4306_);
    return v_res_4312_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(
    mut v_sz_4313_: usize,
    mut v_i_4314_: usize,
    mut v_bs_4315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4316_: u8 = 0;
    let mut v_v_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: usize = 0;
    let mut v___x_4324_: usize = 0;
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4316_ = lean_usize_dec_lt(v_i_4314_, v_sz_4313_);
                if v___x_4316_ == 0 {
                    return v_bs_4315_;
                } else {
                    v_v_4317_ = lean_array_uget_borrowed(v_bs_4315_, v_i_4314_);
                    v_name_4318_ = lean_ctor_get(v_v_4317_, 1);
                    lean_inc(v_name_4318_);
                    v___x_4319_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4320_ = lean_array_uset(v_bs_4315_, v_i_4314_, v___x_4319_);
                    v___x_4321_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_4318_,
                        v___x_4316_,
                    );
                    v___x_4322_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_4322_, 0, v___x_4321_);
                    v___x_4323_ = 1usize;
                    v___x_4324_ = lean_usize_add(v_i_4314_, v___x_4323_);
                    v___x_4325_ = lean_array_uset(v_bs_x27_4320_, v_i_4314_, v___x_4322_);
                    v_i_4314_ = v___x_4324_;
                    v_bs_4315_ = v___x_4325_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(
    mut v_sz_4327_: *mut LeanObject,
    mut v_i_4328_: *mut LeanObject,
    mut v_bs_4329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4330_: usize = 0;
    let mut v_i_boxed_4331_: usize = 0;
    let mut v_res_4332_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4330_ = lean_unbox_usize(v_sz_4327_);
    lean_dec(v_sz_4327_);
    v_i_boxed_4331_ = lean_unbox_usize(v_i_4328_);
    lean_dec(v_i_4328_);
    v_res_4332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_4330_, v_i_boxed_4331_, v_bs_4329_);
    return v_res_4332_;
}
pub unsafe fn l_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(
    mut v_a_4333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4334_: usize = 0;
    let mut v___x_4335_: usize = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4334_ = lean_array_size(v_a_4333_);
    v___x_4335_ = 0usize;
    v___x_4336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_4334_, v___x_4335_, v_a_4333_);
    v___x_4337_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_4337_, 0, v___x_4336_);
    return v___x_4337_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(
    mut v_as_4339_: *mut LeanObject,
    mut v_i_4340_: usize,
    mut v_stop_4341_: usize,
    mut v_b_4342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4343_: u8 = 0;
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: u8 = 0;
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: usize = 0;
    let mut v___x_4352_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4343_ = lean_usize_dec_eq(v_i_4340_, v_stop_4341_);
                if v___x_4343_ == 0 {
                    v___x_4344_ = lean_array_uget_borrowed(v_as_4339_, v_i_4340_);
                    v_name_4345_ = lean_ctor_get(v___x_4344_, 1);
                    v___x_4346_ = 1;
                    lean_inc(v_name_4345_);
                    v___x_4347_ = l_Lean_Name_toString(v_name_4345_, v___x_4346_);
                    v___x_4348_ = lean_string_append(v_b_4342_, v___x_4347_);
                    lean_dec_ref(v___x_4347_);
                    v___x_4349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0;
                    v___x_4350_ = lean_string_append(v___x_4348_, v___x_4349_);
                    v___x_4351_ = 1usize;
                    v___x_4352_ = lean_usize_add(v_i_4340_, v___x_4351_);
                    v_i_4340_ = v___x_4352_;
                    v_b_4342_ = v___x_4350_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4342_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(
    mut v_as_4354_: *mut LeanObject,
    mut v_i_4355_: *mut LeanObject,
    mut v_stop_4356_: *mut LeanObject,
    mut v_b_4357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4358_: usize = 0;
    let mut v_stop_boxed_4359_: usize = 0;
    let mut v_res_4360_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4358_ = lean_unbox_usize(v_i_4355_);
    lean_dec(v_i_4355_);
    v_stop_boxed_4359_ = lean_unbox_usize(v_stop_4356_);
    lean_dec(v_stop_4356_);
    v_res_4360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_4354_, v_i_boxed_4358_, v_stop_boxed_4359_, v_b_4357_);
    lean_dec_ref(v_as_4354_);
    return v_res_4360_;
}
pub unsafe fn l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(
    mut v_fmt_4361_: u8,
    mut v_a_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: u8 = 0;
    let mut v___x_4376_: usize = 0;
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: usize = 0;
    let mut v___x_4380_: usize = 0;
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_fmt_4361_ == 0 {
                    v___x_4371_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0;
                    v___x_4372_ = lean_unsigned_to_nat(0);
                    v___x_4373_ = lean_array_get_size(v_a_4362_);
                    v___x_4374_ = lean_nat_dec_lt(v___x_4372_, v___x_4373_);
                    if v___x_4374_ == 0 {
                        lean_dec_ref(v_a_4362_);
                        v___y_4364_ = v___x_4371_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4375_ = lean_nat_dec_le(v___x_4373_, v___x_4373_);
                        if v___x_4375_ == 0 {
                            if v___x_4374_ == 0 {
                                lean_dec_ref(v_a_4362_);
                                v___y_4364_ = v___x_4371_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4376_ = 0usize;
                                v___x_4377_ = lean_usize_of_nat(v___x_4373_);
                                v___x_4378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_4362_, v___x_4376_, v___x_4377_, v___x_4371_);
                                lean_dec_ref(v_a_4362_);
                                v___y_4364_ = v___x_4378_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_4379_ = 0usize;
                            v___x_4380_ = lean_usize_of_nat(v___x_4373_);
                            v___x_4381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_4362_, v___x_4379_, v___x_4380_, v___x_4371_);
                            lean_dec_ref(v_a_4362_);
                            v___y_4364_ = v___x_4381_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_4382_ = l_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_4362_);
                    v___x_4383_ = l_Lean_Json_compress(v___x_4382_);
                    return v___x_4383_;
                }
            }
            1 => {
                v___x_4365_ = lean_unsigned_to_nat(1);
                v___x_4366_ = lean_unsigned_to_nat(0);
                v___x_4367_ = lean_string_utf8_byte_size(v___y_4364_);
                lean_inc_ref(v___y_4364_);
                v___x_4368_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4368_, 0, v___y_4364_);
                lean_ctor_set(v___x_4368_, 1, v___x_4366_);
                lean_ctor_set(v___x_4368_, 2, v___x_4367_);
                v___x_4369_ = l_String_Slice_Pos_prevn(v___x_4368_, v___x_4367_, v___x_4365_);
                lean_dec_ref_known(v___x_4368_, 3);
                v___x_4370_ = lean_string_utf8_extract(v___y_4364_, v___x_4366_, v___x_4369_);
                lean_dec(v___x_4369_);
                lean_dec_ref(v___y_4364_);
                return v___x_4370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(
    mut v_fmt_4384_: *mut LeanObject,
    mut v_a_4385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_4386_: u8 = 0;
    let mut v_res_4387_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_4386_ = (lean_unbox(v_fmt_4384_) as u8);
    v_res_4387_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_4386_, v_a_4385_);
    return v_res_4387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(
    mut v_as_4401_: *mut LeanObject,
    mut v_i_4402_: usize,
    mut v_stop_4403_: usize,
    mut v_b_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: usize = 0;
    let mut v___x_4427_: usize = 0;
    let mut v_a_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4412_ = lean_usize_dec_eq(v_i_4402_, v_stop_4403_);
                if v___x_4412_ == 0 {
                    v___x_4413_ = lean_array_uget_borrowed(v_as_4401_, v_i_4402_);
                    v_lib_4414_ = lean_ctor_get(v___x_4413_, 0);
                    v_pkg_4415_ = lean_ctor_get(v_lib_4414_, 0);
                    v_name_4416_ = lean_ctor_get(v___x_4413_, 1);
                    v_keyName_4417_ = lean_ctor_get(v_pkg_4415_, 2);
                    v___x_4418_ = l_Lake_Module_leanArtsFacet;
                    lean_inc(v_name_4416_);
                    lean_inc(v_keyName_4417_);
                    v___x_4419_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4419_, 0, v_keyName_4417_);
                    lean_ctor_set(v___x_4419_, 1, v_name_4416_);
                    v___x_4420_ = l_Lake_Module_keyword;
                    lean_inc(v___x_4413_);
                    v___x_4421_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v___x_4421_, 0, v___x_4419_);
                    lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                    lean_ctor_set(v___x_4421_, 2, v___x_4413_);
                    lean_ctor_set(v___x_4421_, 3, v___x_4418_);
                    lean_inc_ref(v___y_4405_);
                    lean_inc_ref(v___y_4409_);
                    lean_inc(v___y_4408_);
                    lean_inc(v___y_4407_);
                    lean_inc(v___y_4406_);
                    v___x_4422_ = lean_apply_7(
                        v___y_4405_,
                        v___x_4421_,
                        v___y_4406_,
                        v___y_4407_,
                        v___y_4408_,
                        v___y_4409_,
                        v___y_4410_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4422_) == 0 {
                        v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
                        lean_inc(v_a_4423_);
                        v_a_4424_ = lean_ctor_get(v___x_4422_, 1);
                        lean_inc(v_a_4424_);
                        lean_dec_ref_known(v___x_4422_, 2);
                        v___x_4425_ = l_Lake_Job_mix___redArg(v_b_4404_, v_a_4423_);
                        v___x_4426_ = 1usize;
                        v___x_4427_ = lean_usize_add(v_i_4402_, v___x_4426_);
                        v_i_4402_ = v___x_4427_;
                        v_b_4404_ = v___x_4425_;
                        v___y_4410_ = v_a_4424_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_4405_);
                        lean_dec_ref(v_b_4404_);
                        v_a_4429_ = lean_ctor_get(v___x_4422_, 0);
                        v_a_4430_ = lean_ctor_get(v___x_4422_, 1);
                        v_isSharedCheck_4437_ = (!lean_is_exclusive(v___x_4422_)) as u8;
                        if v_isSharedCheck_4437_ == 0 {
                            v___x_4432_ = v___x_4422_;
                            v_isShared_4433_ = v_isSharedCheck_4437_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4430_);
                            lean_inc(v_a_4429_);
                            lean_dec(v___x_4422_);
                            v___x_4432_ = lean_box(0);
                            v_isShared_4433_ = v_isSharedCheck_4437_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_4405_);
                    v___x_4438_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4438_, 0, v_b_4404_);
                    lean_ctor_set(v___x_4438_, 1, v___y_4410_);
                    return v___x_4438_;
                }
            }
            1 => {
                if v_isShared_4433_ == 0 {
                    v___x_4435_ = v___x_4432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4429_);
                    lean_ctor_set(v_reuseFailAlloc_4436_, 1, v_a_4430_);
                    v___x_4435_ = v_reuseFailAlloc_4436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(
    mut v_as_4439_: *mut LeanObject,
    mut v_i_4440_: *mut LeanObject,
    mut v_stop_4441_: *mut LeanObject,
    mut v_b_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4450_: usize = 0;
    let mut v_stop_boxed_4451_: usize = 0;
    let mut v_res_4452_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4450_ = lean_unbox_usize(v_i_4440_);
    lean_dec(v_i_4440_);
    v_stop_boxed_4451_ = lean_unbox_usize(v_stop_4441_);
    lean_dec(v_stop_4441_);
    v_res_4452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_4439_, v_i_boxed_4450_, v_stop_boxed_4451_, v_b_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
    lean_dec_ref(v___y_4447_);
    lean_dec(v___y_4446_);
    lean_dec(v___y_4445_);
    lean_dec(v___y_4444_);
    lean_dec_ref(v_as_4439_);
    return v_res_4452_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1()
-> *mut LeanObject {
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4458_: u8 = 0;
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    v___x_4455_ = lean_unsigned_to_nat(0);
    v___x_4456_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once), _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
    v___x_4457_ = 0;
    v___x_4458_ = 0;
    v___x_4459_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0;
    v___x_4460_ = lean_alloc_ctor(0, 3, (2) as u32);
    lean_ctor_set(v___x_4460_, 0, v___x_4459_);
    lean_ctor_set(v___x_4460_, 1, v___x_4456_);
    lean_ctor_set(v___x_4460_, 2, v___x_4455_);
    lean_ctor_set_uint8(
        v___x_4460_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4458_,
    );
    lean_ctor_set_uint8(
        v___x_4460_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
        v___x_4457_,
    );
    return v___x_4460_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2()
-> *mut LeanObject {
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    v___x_4461_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once
        ),
        _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1,
    );
    v___x_4462_ = lean_box(0);
    v___x_4463_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4463_, 0, v___x_4462_);
    lean_ctor_set(v___x_4463_, 1, v___x_4461_);
    return v___x_4463_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3()
-> *mut LeanObject {
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    v___x_4464_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once
        ),
        _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2,
    );
    v___x_4465_ = lean_task_pure(v___x_4464_);
    return v___x_4465_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4()
-> *mut LeanObject {
    let mut v___x_4466_: u8 = 0;
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    v___x_4466_ = 0;
    v___x_4467_ =
        l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0;
    v___x_4468_ = lean_box(0);
    v___x_4469_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once
        ),
        _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3,
    );
    v___x_4470_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_4470_, 0, v___x_4469_);
    lean_ctor_set(v___x_4470_, 1, v___x_4468_);
    lean_ctor_set(v___x_4470_, 2, v___x_4467_);
    lean_ctor_set_uint8(
        v___x_4470_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4466_,
    );
    return v___x_4470_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(
    mut v_self_4471_: *mut LeanObject,
    mut v_a_4472_: *mut LeanObject,
    mut v_a_4473_: *mut LeanObject,
    mut v_a_4474_: *mut LeanObject,
    mut v_a_4475_: *mut LeanObject,
    mut v_a_4476_: *mut LeanObject,
    mut v_a_4477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: u8 = 0;
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: usize = 0;
    let mut v___x_4507_: usize = 0;
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: usize = 0;
    let mut v___x_4510_: usize = 0;
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4512_: u8 = 0;
    let mut v_a_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4521_: u8 = 0;
    let mut v_a_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_4479_ = lean_ctor_get(v_self_4471_, 0);
                v_name_4480_ = lean_ctor_get(v_self_4471_, 1);
                v_keyName_4481_ = lean_ctor_get(v_pkg_4479_, 2);
                v___x_4482_ = l_Lake_LeanLib_modulesFacet;
                lean_inc(v_name_4480_);
                lean_inc(v_keyName_4481_);
                v___x_4483_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_4483_, 0, v_keyName_4481_);
                lean_ctor_set(v___x_4483_, 1, v_name_4480_);
                v___x_4484_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
                v___x_4485_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_4485_, 0, v___x_4483_);
                lean_ctor_set(v___x_4485_, 1, v___x_4484_);
                lean_ctor_set(v___x_4485_, 2, v_self_4471_);
                lean_ctor_set(v___x_4485_, 3, v___x_4482_);
                lean_inc_ref(v_a_4472_);
                lean_inc_ref(v_a_4476_);
                lean_inc(v_a_4475_);
                lean_inc(v_a_4474_);
                lean_inc(v_a_4473_);
                v___x_4486_ = lean_apply_7(
                    v_a_4472_,
                    v___x_4485_,
                    v_a_4473_,
                    v_a_4474_,
                    v_a_4475_,
                    v_a_4476_,
                    v_a_4477_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4486_) == 0 {
                    v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
                    lean_inc(v_a_4487_);
                    v_a_4488_ = lean_ctor_get(v___x_4486_, 1);
                    lean_inc(v_a_4488_);
                    lean_dec_ref_known(v___x_4486_, 2);
                    v___x_4489_ = l_Lake_Job_await___redArg(v_a_4487_, v_a_4488_);
                    if lean_obj_tag(v___x_4489_) == 0 {
                        v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
                        v_a_4491_ = lean_ctor_get(v___x_4489_, 1);
                        v_isSharedCheck_4512_ = (!lean_is_exclusive(v___x_4489_)) as u8;
                        if v_isSharedCheck_4512_ == 0 {
                            v___x_4493_ = v___x_4489_;
                            v_isShared_4494_ = v_isSharedCheck_4512_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4491_);
                            lean_inc(v_a_4490_);
                            lean_dec(v___x_4489_);
                            v___x_4493_ = lean_box(0);
                            v_isShared_4494_ = v_isSharedCheck_4512_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_4472_);
                        v_a_4513_ = lean_ctor_get(v___x_4489_, 0);
                        v_a_4514_ = lean_ctor_get(v___x_4489_, 1);
                        v_isSharedCheck_4521_ = (!lean_is_exclusive(v___x_4489_)) as u8;
                        if v_isSharedCheck_4521_ == 0 {
                            v___x_4516_ = v___x_4489_;
                            v_isShared_4517_ = v_isSharedCheck_4521_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4514_);
                            lean_inc(v_a_4513_);
                            lean_dec(v___x_4489_);
                            v___x_4516_ = lean_box(0);
                            v_isShared_4517_ = v_isSharedCheck_4521_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_4472_);
                    v_a_4522_ = lean_ctor_get(v___x_4486_, 0);
                    v_a_4523_ = lean_ctor_get(v___x_4486_, 1);
                    v_isSharedCheck_4530_ = (!lean_is_exclusive(v___x_4486_)) as u8;
                    if v_isSharedCheck_4530_ == 0 {
                        v___x_4525_ = v___x_4486_;
                        v_isShared_4526_ = v_isSharedCheck_4530_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4523_);
                        lean_inc(v_a_4522_);
                        lean_dec(v___x_4486_);
                        v___x_4525_ = lean_box(0);
                        v_isShared_4526_ = v_isSharedCheck_4530_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4495_ = lean_unsigned_to_nat(0);
                v___x_4496_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once), _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
                v___x_4497_ = lean_array_get_size(v_a_4490_);
                v___x_4498_ = lean_nat_dec_lt(v___x_4495_, v___x_4497_);
                if v___x_4498_ == 0 {
                    lean_dec(v_a_4490_);
                    lean_dec_ref(v_a_4472_);
                    if v_isShared_4494_ == 0 {
                        lean_ctor_set(v___x_4493_, 0, v___x_4496_);
                        v___x_4500_ = v___x_4493_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4496_);
                        lean_ctor_set(v_reuseFailAlloc_4501_, 1, v_a_4491_);
                        v___x_4500_ = v_reuseFailAlloc_4501_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4502_ = lean_nat_dec_le(v___x_4497_, v___x_4497_);
                    if v___x_4502_ == 0 {
                        if v___x_4498_ == 0 {
                            lean_dec(v_a_4490_);
                            lean_dec_ref(v_a_4472_);
                            if v_isShared_4494_ == 0 {
                                lean_ctor_set(v___x_4493_, 0, v___x_4496_);
                                v___x_4504_ = v___x_4493_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4496_);
                                lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_a_4491_);
                                v___x_4504_ = v_reuseFailAlloc_4505_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4493_);
                            v___x_4506_ = 0usize;
                            v___x_4507_ = lean_usize_of_nat(v___x_4497_);
                            v___x_4508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_4490_, v___x_4506_, v___x_4507_, v___x_4496_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4491_);
                            lean_dec(v_a_4490_);
                            return v___x_4508_;
                        }
                    } else {
                        lean_del_object(v___x_4493_);
                        v___x_4509_ = 0usize;
                        v___x_4510_ = lean_usize_of_nat(v___x_4497_);
                        v___x_4511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_4490_, v___x_4509_, v___x_4510_, v___x_4496_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4491_);
                        lean_dec(v_a_4490_);
                        return v___x_4511_;
                    }
                }
            }
            2 => {
                return v___x_4500_;
            }
            3 => {
                return v___x_4504_;
            }
            4 => {
                if v_isShared_4517_ == 0 {
                    v___x_4519_ = v___x_4516_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4513_);
                    lean_ctor_set(v_reuseFailAlloc_4520_, 1, v_a_4514_);
                    v___x_4519_ = v_reuseFailAlloc_4520_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4519_;
            }
            6 => {
                if v_isShared_4526_ == 0 {
                    v___x_4528_ = v___x_4525_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4522_);
                    lean_ctor_set(v_reuseFailAlloc_4529_, 1, v_a_4523_);
                    v___x_4528_ = v_reuseFailAlloc_4529_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(
    mut v_self_4531_: *mut LeanObject,
    mut v_a_4532_: *mut LeanObject,
    mut v_a_4533_: *mut LeanObject,
    mut v_a_4534_: *mut LeanObject,
    mut v_a_4535_: *mut LeanObject,
    mut v_a_4536_: *mut LeanObject,
    mut v_a_4537_: *mut LeanObject,
    mut v_a_4538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4539_: *mut LeanObject = core::ptr::null_mut();
    v_res_4539_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(
        v_self_4531_,
        v_a_4532_,
        v_a_4533_,
        v_a_4534_,
        v_a_4535_,
        v_a_4536_,
        v_a_4537_,
    );
    lean_dec_ref(v_a_4536_);
    lean_dec(v_a_4535_);
    lean_dec(v_a_4534_);
    lean_dec(v_a_4533_);
    return v_res_4539_;
}
pub unsafe fn _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    v___x_4540_ = lean_box(0);
    v___x_4541_ = l_Lean_Json_compress(v___x_4540_);
    return v___x_4541_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(
    mut v_fmt_4542_: u8,
) -> *mut LeanObject {
    if v_fmt_4542_ == 0 {
        let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
        v___x_4543_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0;
        return v___x_4543_;
    } else {
        let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
        v___x_4544_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once), _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
        return v___x_4544_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(
    mut v_fmt_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_4546_: u8 = 0;
    let mut v_res_4547_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_4546_ = (lean_unbox(v_fmt_4545_) as u8);
    v_res_4547_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(
        v_fmt_boxed_4546_,
    );
    return v_res_4547_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(
    mut v_fmt_4548_: u8,
    mut v_a_4549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    v___x_4550_ =
        l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_4548_);
    return v___x_4550_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(
    mut v_fmt_4551_: *mut LeanObject,
    mut v_a_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_4553_: u8 = 0;
    let mut v_res_4554_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_4553_ = (lean_unbox(v_fmt_4551_) as u8);
    v_res_4554_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(
        v_fmt_boxed_4553_,
        v_a_4552_,
    );
    return v_res_4554_;
}
pub unsafe fn l_Lake_LeanLib_leanArtsFacetConfig___lam__0(
    mut v___y_4555_: u8,
    mut v___y_4556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    v___x_4557_ =
        l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_4555_);
    return v___x_4557_;
}
pub unsafe fn l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_68__boxed_4560_: u8 = 0;
    let mut v_res_4561_: *mut LeanObject = core::ptr::null_mut();
    v___y_68__boxed_4560_ = (lean_unbox(v___y_4558_) as u8);
    v_res_4561_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_4560_, v___y_4559_);
    return v_res_4561_;
}
pub unsafe fn _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___f_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: u8 = 0;
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    v___f_4564_ = l_Lake_LeanLib_leanArtsFacetConfig___closed__0;
    v___x_4565_ = 1;
    v___x_4566_ = l_Lake_instDataKindUnit;
    v___x_4567_ = l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
    v___x_4568_ = l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
    v___x_4569_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_4569_, 0, v___x_4568_);
    lean_ctor_set(v___x_4569_, 1, v___x_4567_);
    lean_ctor_set(v___x_4569_, 2, v___x_4566_);
    lean_ctor_set(v___x_4569_, 3, v___f_4564_);
    lean_ctor_set_uint8(
        v___x_4569_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_4565_,
    );
    lean_ctor_set_uint8(
        v___x_4569_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_4565_,
    );
    return v___x_4569_;
}
pub unsafe fn _init_l_Lake_LeanLib_leanArtsFacetConfig() -> *mut LeanObject {
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    v___x_4570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_leanArtsFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once),
        _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2,
    );
    return v___x_4570_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(
    mut v_a_4571_: *mut LeanObject,
    mut v_x_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
    mut v___y_4578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    v___x_4580_ = l_Lake_ModuleFacet_fetch___redArg(
        v_x_4572_,
        v_a_4571_,
        v___y_4573_,
        v___y_4574_,
        v___y_4575_,
        v___y_4576_,
        v___y_4577_,
        v___y_4578_,
    );
    return v___x_4580_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(
    mut v_a_4581_: *mut LeanObject,
    mut v_x_4582_: *mut LeanObject,
    mut v___y_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4590_: *mut LeanObject = core::ptr::null_mut();
    v_res_4590_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(
        v_a_4581_,
        v_x_4582_,
        v___y_4583_,
        v___y_4584_,
        v___y_4585_,
        v___y_4586_,
        v___y_4587_,
        v___y_4588_,
    );
    lean_dec_ref(v___y_4587_);
    lean_dec(v___y_4586_);
    lean_dec(v___y_4585_);
    lean_dec(v___y_4584_);
    return v_res_4590_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(
    mut v_shouldExport_4591_: u8,
    mut v___x_4592_: *mut LeanObject,
    mut v_bs_4593_: *mut LeanObject,
    mut v_a_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lib_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4608_: usize = 0;
    let mut v___x_4609_: usize = 0;
    let mut v___x_196942__overap_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4616_: u8 = 0;
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_4602_ = lean_ctor_get(v_a_4594_, 0);
                v_config_4603_ = lean_ctor_get(v_lib_4602_, 2);
                v_nativeFacets_4604_ = lean_ctor_get(v_config_4603_, 8);
                lean_inc_ref(v_nativeFacets_4604_);
                v___f_4605_ = lean_alloc_closure(
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    1,
                );
                lean_closure_set(v___f_4605_, 0, v_a_4594_);
                v___x_4606_ = lean_box((v_shouldExport_4591_) as usize);
                v___x_4607_ = lean_apply_1(v_nativeFacets_4604_, v___x_4606_);
                v_sz_4608_ = lean_array_size(v___x_4607_);
                v___x_4609_ = 0usize;
                v___x_196942__overap_4610_ =
                    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_4592_,
                        v___f_4605_,
                        v_sz_4608_,
                        v___x_4609_,
                        v___x_4607_,
                    );
                lean_inc_ref(v___y_4599_);
                lean_inc(v___y_4598_);
                lean_inc(v___y_4597_);
                lean_inc(v___y_4596_);
                v___x_4611_ = lean_apply_7(
                    v___x_196942__overap_4610_,
                    v___y_4595_,
                    v___y_4596_,
                    v___y_4597_,
                    v___y_4598_,
                    v___y_4599_,
                    v___y_4600_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4611_) == 0 {
                    v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
                    v_a_4613_ = lean_ctor_get(v___x_4611_, 1);
                    v_isSharedCheck_4621_ = (!lean_is_exclusive(v___x_4611_)) as u8;
                    if v_isSharedCheck_4621_ == 0 {
                        v___x_4615_ = v___x_4611_;
                        v_isShared_4616_ = v_isSharedCheck_4621_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4613_);
                        lean_inc(v_a_4612_);
                        lean_dec(v___x_4611_);
                        v___x_4615_ = lean_box(0);
                        v_isShared_4616_ = v_isSharedCheck_4621_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_bs_4593_);
                    return v___x_4611_;
                }
            }
            1 => {
                v___x_4617_ = l_Array_append___redArg(v_bs_4593_, v_a_4612_);
                lean_dec(v_a_4612_);
                if v_isShared_4616_ == 0 {
                    lean_ctor_set(v___x_4615_, 0, v___x_4617_);
                    v___x_4619_ = v___x_4615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_a_4613_);
                    v___x_4619_ = v_reuseFailAlloc_4620_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(
    mut v_shouldExport_4622_: *mut LeanObject,
    mut v___x_4623_: *mut LeanObject,
    mut v_bs_4624_: *mut LeanObject,
    mut v_a_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
    mut v___y_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldExport_boxed_4633_: u8 = 0;
    let mut v_res_4634_: *mut LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_4633_ = (lean_unbox(v_shouldExport_4622_) as u8);
    v_res_4634_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(
        v_shouldExport_boxed_4633_,
        v___x_4623_,
        v_bs_4624_,
        v_a_4625_,
        v___y_4626_,
        v___y_4627_,
        v___y_4628_,
        v___y_4629_,
        v___y_4630_,
        v___y_4631_,
    );
    lean_dec_ref(v___y_4630_);
    lean_dec(v___y_4629_);
    lean_dec(v___y_4628_);
    lean_dec(v___y_4627_);
    return v_res_4634_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(
    mut v___x_4635_: *mut LeanObject,
    mut v_pkg_4636_: *mut LeanObject,
    mut v_x_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
    mut v___y_4641_: *mut LeanObject,
    mut v___y_4642_: *mut LeanObject,
    mut v___y_4643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    v___x_4645_ = l_Lake_Target_fetchIn___redArg(
        v___x_4635_,
        v_pkg_4636_,
        v_x_4637_,
        v___y_4638_,
        v___y_4639_,
        v___y_4640_,
        v___y_4641_,
        v___y_4642_,
        v___y_4643_,
    );
    return v___x_4645_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(
    mut v___x_4646_: *mut LeanObject,
    mut v_pkg_4647_: *mut LeanObject,
    mut v_x_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4656_: *mut LeanObject = core::ptr::null_mut();
    v_res_4656_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(
        v___x_4646_,
        v_pkg_4647_,
        v_x_4648_,
        v___y_4649_,
        v___y_4650_,
        v___y_4651_,
        v___y_4652_,
        v___y_4653_,
        v___y_4654_,
    );
    lean_dec_ref(v___y_4653_);
    lean_dec(v___y_4652_);
    lean_dec(v___y_4651_);
    lean_dec(v___y_4650_);
    return v_res_4656_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(
    mut v_a_4657_: *mut LeanObject,
    mut v_x_4658_: *mut LeanObject,
    mut v___y_4659_: *mut LeanObject,
    mut v___y_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_log_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4668_: u8 = 0;
    let mut v_wantsRebuild_4669_: u8 = 0;
    let mut v_trace_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4679_: u8 = 0;
    let mut v_a_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4690_: u8 = 0;
    let mut v_unused_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_4667_ = lean_ctor_get(v___y_4665_, 0);
                v_action_4668_ = lean_ctor_get_uint8(
                    v___y_4665_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4669_ = lean_ctor_get_uint8(
                    v___y_4665_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4670_ = lean_ctor_get(v___y_4665_, 1);
                v_buildTime_4671_ = lean_ctor_get(v___y_4665_, 2);
                v___x_4672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0;
                v___x_4673_ = lean_string_append(v___y_4659_, v___x_4672_);
                v___x_4674_ = lean_io_prim_handle_put_str(v_a_4657_, v___x_4673_);
                lean_dec_ref(v___x_4673_);
                if lean_obj_tag(v___x_4674_) == 0 {
                    v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
                    lean_inc(v_a_4675_);
                    lean_dec_ref_known(v___x_4674_, 1);
                    v___x_4676_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4676_, 0, v_a_4675_);
                    lean_ctor_set(v___x_4676_, 1, v___y_4665_);
                    return v___x_4676_;
                } else {
                    lean_inc(v_buildTime_4671_);
                    lean_inc_ref(v_trace_4670_);
                    lean_inc_ref(v_log_4667_);
                    v_isSharedCheck_4690_ = (!lean_is_exclusive(v___y_4665_)) as u8;
                    if v_isSharedCheck_4690_ == 0 {
                        v_unused_4691_ = lean_ctor_get(v___y_4665_, 2);
                        lean_dec(v_unused_4691_);
                        v_unused_4692_ = lean_ctor_get(v___y_4665_, 1);
                        lean_dec(v_unused_4692_);
                        v_unused_4693_ = lean_ctor_get(v___y_4665_, 0);
                        lean_dec(v_unused_4693_);
                        v___x_4678_ = v___y_4665_;
                        v_isShared_4679_ = v_isSharedCheck_4690_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___y_4665_);
                        v___x_4678_ = lean_box(0);
                        v_isShared_4679_ = v_isSharedCheck_4690_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4680_ = lean_ctor_get(v___x_4674_, 0);
                lean_inc(v_a_4680_);
                lean_dec_ref_known(v___x_4674_, 1);
                v___x_4681_ = lean_io_error_to_string(v_a_4680_);
                v___x_4682_ = 3;
                v___x_4683_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4683_, 0, v___x_4681_);
                lean_ctor_set_uint8(
                    v___x_4683_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4682_,
                );
                v___x_4684_ = lean_array_get_size(v_log_4667_);
                v___x_4685_ = lean_array_push(v_log_4667_, v___x_4683_);
                if v_isShared_4679_ == 0 {
                    lean_ctor_set(v___x_4678_, 0, v___x_4685_);
                    v___x_4687_ = v___x_4678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4685_);
                    lean_ctor_set(v_reuseFailAlloc_4689_, 1, v_trace_4670_);
                    lean_ctor_set(v_reuseFailAlloc_4689_, 2, v_buildTime_4671_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4689_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4668_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4689_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4669_,
                    );
                    v___x_4687_ = v_reuseFailAlloc_4689_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4688_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4688_, 0, v___x_4684_);
                lean_ctor_set(v___x_4688_, 1, v___x_4687_);
                return v___x_4688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(
    mut v_a_4694_: *mut LeanObject,
    mut v_x_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
    mut v___y_4698_: *mut LeanObject,
    mut v___y_4699_: *mut LeanObject,
    mut v___y_4700_: *mut LeanObject,
    mut v___y_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4704_: *mut LeanObject = core::ptr::null_mut();
    v_res_4704_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(
        v_a_4694_,
        v_x_4695_,
        v___y_4696_,
        v___y_4697_,
        v___y_4698_,
        v___y_4699_,
        v___y_4700_,
        v___y_4701_,
        v___y_4702_,
    );
    lean_dec_ref(v___y_4701_);
    lean_dec(v___y_4700_);
    lean_dec(v___y_4699_);
    lean_dec(v___y_4698_);
    lean_dec_ref(v___y_4697_);
    lean_dec(v_a_4694_);
    return v_res_4704_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6()
-> *mut LeanObject {
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    v___x_4712_ =
        l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3;
    v___x_4713_ = lean_unsigned_to_nat(5);
    v___x_4714_ = lean_mk_empty_array_with_capacity(v___x_4713_);
    v___x_4715_ = lean_array_push(v___x_4714_, v___x_4712_);
    return v___x_4715_;
}
pub unsafe fn _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7()
-> *mut LeanObject {
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    v___x_4716_ =
        l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4;
    v___x_4717_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once
        ),
        _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6,
    );
    v___x_4718_ = lean_array_push(v___x_4717_, v___x_4716_);
    return v___x_4718_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(
    mut v_bootstrap_4721_: u8,
    mut v___y_4722_: *mut LeanObject,
    mut v_oFiles_4723_: *mut LeanObject,
    mut v_shouldExport_4724_: u8,
    mut v___x_4725_: u8,
    mut v___x_4726_: *mut LeanObject,
    mut v___x_4727_: usize,
    mut v___y_4728_: *mut LeanObject,
    mut v___y_4729_: *mut LeanObject,
    mut v___y_4730_: *mut LeanObject,
    mut v___y_4731_: *mut LeanObject,
    mut v___y_4732_: *mut LeanObject,
    mut v___y_4733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4739_: u8 = 0;
    let mut v_wantsRebuild_4740_: u8 = 0;
    let mut v_trace_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4745_: u8 = 0;
    let mut v_ar_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4752_: u8 = 0;
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut v_a_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4764_: u8 = 0;
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4771_: u8 = 0;
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: u8 = 0;
    let mut v_toContext_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4779_: u8 = 0;
    let mut v_wantsRebuild_4780_: u8 = 0;
    let mut v_trace_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4785_: u8 = 0;
    let mut v_ar_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4792_: u8 = 0;
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut v_a_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4804_: u8 = 0;
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4811_: u8 = 0;
    let mut v_isSharedCheck_4812_: u8 = 0;
    let mut v_toContext_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4817_: u8 = 0;
    let mut v_wantsRebuild_4818_: u8 = 0;
    let mut v_trace_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4823_: u8 = 0;
    let mut v_ar_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4830_: u8 = 0;
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4837_: u8 = 0;
    let mut v_a_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_isSharedCheck_4850_: u8 = 0;
    let mut v_log_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4852_: u8 = 0;
    let mut v_wantsRebuild_4853_: u8 = 0;
    let mut v_trace_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4863_: u8 = 0;
    let mut v_wantsRebuild_4864_: u8 = 0;
    let mut v_trace_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4885_: u8 = 0;
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4892_: u8 = 0;
    let mut v_a_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4897_: u8 = 0;
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4904_: u8 = 0;
    let mut v_isSharedCheck_4905_: u8 = 0;
    let mut v___y_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: u8 = 0;
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: u8 = 0;
    let mut v___f_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: u8 = 0;
    let mut v___x_4919_: usize = 0;
    let mut v___x_197100__overap_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: usize = 0;
    let mut v___x_197102__overap_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v_a_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: u8 = 0;
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_unused_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v_a_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: u8 = 0;
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut v_unused_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_bootstrap_4721_ == 0 {
                    lean_dec_ref(v___y_4728_);
                    lean_dec_ref(v___x_4726_);
                    v_toContext_4735_ = lean_ctor_get(v___y_4732_, 1);
                    v_lakeEnv_4736_ = lean_ctor_get(v_toContext_4735_, 0);
                    v_lean_4737_ = lean_ctor_get(v_lakeEnv_4736_, 1);
                    v_log_4738_ = lean_ctor_get(v___y_4733_, 0);
                    v_action_4739_ = lean_ctor_get_uint8(
                        v___y_4733_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_4740_ = lean_ctor_get_uint8(
                        v___y_4733_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_4741_ = lean_ctor_get(v___y_4733_, 1);
                    v_buildTime_4742_ = lean_ctor_get(v___y_4733_, 2);
                    v_isSharedCheck_4772_ = (!lean_is_exclusive(v___y_4733_)) as u8;
                    if v_isSharedCheck_4772_ == 0 {
                        v___x_4744_ = v___y_4733_;
                        v_isShared_4745_ = v_isSharedCheck_4772_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_buildTime_4742_);
                        lean_inc(v_trace_4741_);
                        lean_inc(v_log_4738_);
                        lean_dec(v___y_4733_);
                        v___x_4744_ = lean_box(0);
                        v_isShared_4745_ = v_isSharedCheck_4772_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4773_ = l_System_Platform_isOSX;
                    if v___x_4773_ == 0 {
                        lean_dec_ref(v___y_4728_);
                        lean_dec_ref(v___x_4726_);
                        v___x_4774_ = l_System_Platform_isWindows;
                        if v___x_4774_ == 0 {
                            v_toContext_4775_ = lean_ctor_get(v___y_4732_, 1);
                            v_lakeEnv_4776_ = lean_ctor_get(v_toContext_4775_, 0);
                            v_lean_4777_ = lean_ctor_get(v_lakeEnv_4776_, 1);
                            v_log_4778_ = lean_ctor_get(v___y_4733_, 0);
                            v_action_4779_ = lean_ctor_get_uint8(
                                v___y_4733_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            v_wantsRebuild_4780_ = lean_ctor_get_uint8(
                                v___y_4733_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            );
                            v_trace_4781_ = lean_ctor_get(v___y_4733_, 1);
                            v_buildTime_4782_ = lean_ctor_get(v___y_4733_, 2);
                            v_isSharedCheck_4812_ = (!lean_is_exclusive(v___y_4733_)) as u8;
                            if v_isSharedCheck_4812_ == 0 {
                                v___x_4784_ = v___y_4733_;
                                v_isShared_4785_ = v_isSharedCheck_4812_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_buildTime_4782_);
                                lean_inc(v_trace_4781_);
                                lean_inc(v_log_4778_);
                                lean_dec(v___y_4733_);
                                v___x_4784_ = lean_box(0);
                                v_isShared_4785_ = v_isSharedCheck_4812_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_toContext_4813_ = lean_ctor_get(v___y_4732_, 1);
                            v_lakeEnv_4814_ = lean_ctor_get(v_toContext_4813_, 0);
                            v_lean_4815_ = lean_ctor_get(v_lakeEnv_4814_, 1);
                            v_log_4816_ = lean_ctor_get(v___y_4733_, 0);
                            v_action_4817_ = lean_ctor_get_uint8(
                                v___y_4733_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            v_wantsRebuild_4818_ = lean_ctor_get_uint8(
                                v___y_4733_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            );
                            v_trace_4819_ = lean_ctor_get(v___y_4733_, 1);
                            v_buildTime_4820_ = lean_ctor_get(v___y_4733_, 2);
                            v_isSharedCheck_4850_ = (!lean_is_exclusive(v___y_4733_)) as u8;
                            if v_isSharedCheck_4850_ == 0 {
                                v___x_4822_ = v___y_4733_;
                                v_isShared_4823_ = v_isSharedCheck_4850_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_buildTime_4820_);
                                lean_inc(v_trace_4819_);
                                lean_inc(v_log_4816_);
                                lean_dec(v___y_4733_);
                                v___x_4822_ = lean_box(0);
                                v_isShared_4823_ = v_isSharedCheck_4850_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        v_log_4851_ = lean_ctor_get(v___y_4733_, 0);
                        v_action_4852_ = lean_ctor_get_uint8(
                            v___y_4733_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_wantsRebuild_4853_ = lean_ctor_get_uint8(
                            v___y_4733_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_trace_4854_ = lean_ctor_get(v___y_4733_, 1);
                        v_buildTime_4855_ = lean_ctor_get(v___y_4733_, 2);
                        lean_inc_ref(v___y_4722_);
                        v___x_4856_ = l_Lake_createParentDirs(v___y_4722_);
                        if lean_obj_tag(v___x_4856_) == 0 {
                            lean_dec_ref_known(v___x_4856_, 1);
                            v___x_4857_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0;
                            lean_inc_ref(v___y_4722_);
                            v___x_4858_ = l_System_FilePath_addExtension(v___y_4722_, v___x_4857_);
                            v___x_4909_ = 1;
                            v___x_4910_ = lean_io_prim_handle_mk(v___x_4858_, v___x_4909_);
                            if lean_obj_tag(v___x_4910_) == 0 {
                                v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
                                lean_inc(v_a_4911_);
                                lean_dec_ref_known(v___x_4910_, 1);
                                v___x_4912_ = l_Lake_EquipT_instMonad___redArg(v___x_4726_);
                                v___x_4913_ = lean_unsigned_to_nat(0);
                                v___x_4914_ = lean_array_get_size(v_oFiles_4723_);
                                v___x_4915_ = lean_nat_dec_lt(v___x_4913_, v___x_4914_);
                                if v___x_4915_ == 0 {
                                    lean_dec_ref(v___x_4912_);
                                    lean_dec(v_a_4911_);
                                    lean_dec_ref(v___y_4728_);
                                    lean_dec_ref(v_oFiles_4723_);
                                    v_a_4860_ = v___y_4733_;
                                    state = 22;
                                    continue;
                                } else {
                                    v___f_4916_ = lean_alloc_closure(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed as *mut core::ffi::c_void, 10, 1);
                                    lean_closure_set(v___f_4916_, 0, v_a_4911_);
                                    v___x_4917_ = lean_box(0);
                                    v___x_4918_ = lean_nat_dec_le(v___x_4914_, v___x_4914_);
                                    if v___x_4918_ == 0 {
                                        if v___x_4915_ == 0 {
                                            lean_dec_ref(v___f_4916_);
                                            lean_dec_ref(v___x_4912_);
                                            lean_dec_ref(v___y_4728_);
                                            lean_dec_ref(v_oFiles_4723_);
                                            v_a_4860_ = v___y_4733_;
                                            state = 22;
                                            continue;
                                        } else {
                                            v___x_4919_ = lean_usize_of_nat(v___x_4914_);
                                            v___x_197100__overap_4920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4912_, v___f_4916_, v_oFiles_4723_, v___x_4727_, v___x_4919_, v___x_4917_);
                                            lean_inc_ref(v___y_4732_);
                                            lean_inc(v___y_4731_);
                                            lean_inc(v___y_4730_);
                                            lean_inc(v___y_4729_);
                                            v___x_4921_ = lean_apply_7(
                                                v___x_197100__overap_4920_,
                                                v___y_4728_,
                                                v___y_4729_,
                                                v___y_4730_,
                                                v___y_4731_,
                                                v___y_4732_,
                                                v___y_4733_,
                                                lean_box(0),
                                            );
                                            v___y_4907_ = v___x_4921_;
                                            state = 30;
                                            continue;
                                        }
                                    } else {
                                        v___x_4922_ = lean_usize_of_nat(v___x_4914_);
                                        v___x_197102__overap_4923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4912_, v___f_4916_, v_oFiles_4723_, v___x_4727_, v___x_4922_, v___x_4917_);
                                        lean_inc_ref(v___y_4732_);
                                        lean_inc(v___y_4731_);
                                        lean_inc(v___y_4730_);
                                        lean_inc(v___y_4729_);
                                        v___x_4924_ = lean_apply_7(
                                            v___x_197102__overap_4923_,
                                            v___y_4728_,
                                            v___y_4729_,
                                            v___y_4730_,
                                            v___y_4731_,
                                            v___y_4732_,
                                            v___y_4733_,
                                            lean_box(0),
                                        );
                                        v___y_4907_ = v___x_4924_;
                                        state = 30;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc(v_buildTime_4855_);
                                lean_inc_ref(v_trace_4854_);
                                lean_inc_ref(v_log_4851_);
                                lean_dec_ref(v___x_4858_);
                                lean_dec_ref(v___y_4728_);
                                lean_dec_ref(v___x_4726_);
                                lean_dec_ref(v_oFiles_4723_);
                                lean_dec_ref(v___y_4722_);
                                v_isSharedCheck_4938_ = (!lean_is_exclusive(v___y_4733_)) as u8;
                                if v_isSharedCheck_4938_ == 0 {
                                    v_unused_4939_ = lean_ctor_get(v___y_4733_, 2);
                                    lean_dec(v_unused_4939_);
                                    v_unused_4940_ = lean_ctor_get(v___y_4733_, 1);
                                    lean_dec(v_unused_4940_);
                                    v_unused_4941_ = lean_ctor_get(v___y_4733_, 0);
                                    lean_dec(v_unused_4941_);
                                    v___x_4926_ = v___y_4733_;
                                    v_isShared_4927_ = v_isSharedCheck_4938_;
                                    state = 31;
                                    continue;
                                } else {
                                    lean_dec(v___y_4733_);
                                    v___x_4926_ = lean_box(0);
                                    v_isShared_4927_ = v_isSharedCheck_4938_;
                                    state = 31;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v_buildTime_4855_);
                            lean_inc_ref(v_trace_4854_);
                            lean_inc_ref(v_log_4851_);
                            lean_dec_ref(v___y_4728_);
                            lean_dec_ref(v___x_4726_);
                            lean_dec_ref(v_oFiles_4723_);
                            lean_dec_ref(v___y_4722_);
                            v_isSharedCheck_4955_ = (!lean_is_exclusive(v___y_4733_)) as u8;
                            if v_isSharedCheck_4955_ == 0 {
                                v_unused_4956_ = lean_ctor_get(v___y_4733_, 2);
                                lean_dec(v_unused_4956_);
                                v_unused_4957_ = lean_ctor_get(v___y_4733_, 1);
                                lean_dec(v_unused_4957_);
                                v_unused_4958_ = lean_ctor_get(v___y_4733_, 0);
                                lean_dec(v_unused_4958_);
                                v___x_4943_ = v___y_4733_;
                                v_isShared_4944_ = v_isSharedCheck_4955_;
                                state = 33;
                                continue;
                            } else {
                                lean_dec(v___y_4733_);
                                v___x_4943_ = lean_box(0);
                                v_isShared_4944_ = v_isSharedCheck_4955_;
                                state = 33;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_ar_4746_ = lean_ctor_get(v_lean_4737_, 13);
                lean_inc_ref(v_ar_4746_);
                v___x_4747_ = l_Lake_compileStaticLib(
                    v___y_4722_,
                    v_oFiles_4723_,
                    v_ar_4746_,
                    v_bootstrap_4721_,
                    v_log_4738_,
                );
                if lean_obj_tag(v___x_4747_) == 0 {
                    v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
                    v_a_4749_ = lean_ctor_get(v___x_4747_, 1);
                    v_isSharedCheck_4759_ = (!lean_is_exclusive(v___x_4747_)) as u8;
                    if v_isSharedCheck_4759_ == 0 {
                        v___x_4751_ = v___x_4747_;
                        v_isShared_4752_ = v_isSharedCheck_4759_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4749_);
                        lean_inc(v_a_4748_);
                        lean_dec(v___x_4747_);
                        v___x_4751_ = lean_box(0);
                        v_isShared_4752_ = v_isSharedCheck_4759_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4760_ = lean_ctor_get(v___x_4747_, 0);
                    v_a_4761_ = lean_ctor_get(v___x_4747_, 1);
                    v_isSharedCheck_4771_ = (!lean_is_exclusive(v___x_4747_)) as u8;
                    if v_isSharedCheck_4771_ == 0 {
                        v___x_4763_ = v___x_4747_;
                        v_isShared_4764_ = v_isSharedCheck_4771_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4761_);
                        lean_inc(v_a_4760_);
                        lean_dec(v___x_4747_);
                        v___x_4763_ = lean_box(0);
                        v_isShared_4764_ = v_isSharedCheck_4771_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4745_ == 0 {
                    lean_ctor_set(v___x_4744_, 0, v_a_4749_);
                    v___x_4754_ = v___x_4744_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4749_);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_trace_4741_);
                    lean_ctor_set(v_reuseFailAlloc_4758_, 2, v_buildTime_4742_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4758_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4739_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4758_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4740_,
                    );
                    v___x_4754_ = v_reuseFailAlloc_4758_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4752_ == 0 {
                    lean_ctor_set(v___x_4751_, 1, v___x_4754_);
                    v___x_4756_ = v___x_4751_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4748_);
                    lean_ctor_set(v_reuseFailAlloc_4757_, 1, v___x_4754_);
                    v___x_4756_ = v_reuseFailAlloc_4757_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4756_;
            }
            5 => {
                if v_isShared_4745_ == 0 {
                    lean_ctor_set(v___x_4744_, 0, v_a_4761_);
                    v___x_4766_ = v___x_4744_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4761_);
                    lean_ctor_set(v_reuseFailAlloc_4770_, 1, v_trace_4741_);
                    lean_ctor_set(v_reuseFailAlloc_4770_, 2, v_buildTime_4742_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4770_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4739_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4770_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4740_,
                    );
                    v___x_4766_ = v_reuseFailAlloc_4770_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4764_ == 0 {
                    lean_ctor_set(v___x_4763_, 1, v___x_4766_);
                    v___x_4768_ = v___x_4763_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4760_);
                    lean_ctor_set(v_reuseFailAlloc_4769_, 1, v___x_4766_);
                    v___x_4768_ = v_reuseFailAlloc_4769_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4768_;
            }
            8 => {
                v_ar_4786_ = lean_ctor_get(v_lean_4777_, 13);
                lean_inc_ref(v_ar_4786_);
                v___x_4787_ = l_Lake_compileStaticLib(
                    v___y_4722_,
                    v_oFiles_4723_,
                    v_ar_4786_,
                    v___x_4774_,
                    v_log_4778_,
                );
                if lean_obj_tag(v___x_4787_) == 0 {
                    v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
                    v_a_4789_ = lean_ctor_get(v___x_4787_, 1);
                    v_isSharedCheck_4799_ = (!lean_is_exclusive(v___x_4787_)) as u8;
                    if v_isSharedCheck_4799_ == 0 {
                        v___x_4791_ = v___x_4787_;
                        v_isShared_4792_ = v_isSharedCheck_4799_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4789_);
                        lean_inc(v_a_4788_);
                        lean_dec(v___x_4787_);
                        v___x_4791_ = lean_box(0);
                        v_isShared_4792_ = v_isSharedCheck_4799_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_4800_ = lean_ctor_get(v___x_4787_, 0);
                    v_a_4801_ = lean_ctor_get(v___x_4787_, 1);
                    v_isSharedCheck_4811_ = (!lean_is_exclusive(v___x_4787_)) as u8;
                    if v_isSharedCheck_4811_ == 0 {
                        v___x_4803_ = v___x_4787_;
                        v_isShared_4804_ = v_isSharedCheck_4811_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_4801_);
                        lean_inc(v_a_4800_);
                        lean_dec(v___x_4787_);
                        v___x_4803_ = lean_box(0);
                        v_isShared_4804_ = v_isSharedCheck_4811_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4785_ == 0 {
                    lean_ctor_set(v___x_4784_, 0, v_a_4789_);
                    v___x_4794_ = v___x_4784_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4789_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_trace_4781_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_buildTime_4782_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4798_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4779_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4798_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4780_,
                    );
                    v___x_4794_ = v_reuseFailAlloc_4798_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4792_ == 0 {
                    lean_ctor_set(v___x_4791_, 1, v___x_4794_);
                    v___x_4796_ = v___x_4791_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4788_);
                    lean_ctor_set(v_reuseFailAlloc_4797_, 1, v___x_4794_);
                    v___x_4796_ = v_reuseFailAlloc_4797_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4796_;
            }
            12 => {
                if v_isShared_4785_ == 0 {
                    lean_ctor_set(v___x_4784_, 0, v_a_4801_);
                    v___x_4806_ = v___x_4784_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4801_);
                    lean_ctor_set(v_reuseFailAlloc_4810_, 1, v_trace_4781_);
                    lean_ctor_set(v_reuseFailAlloc_4810_, 2, v_buildTime_4782_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4810_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4779_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4810_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4780_,
                    );
                    v___x_4806_ = v_reuseFailAlloc_4810_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4804_ == 0 {
                    lean_ctor_set(v___x_4803_, 1, v___x_4806_);
                    v___x_4808_ = v___x_4803_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4800_);
                    lean_ctor_set(v_reuseFailAlloc_4809_, 1, v___x_4806_);
                    v___x_4808_ = v_reuseFailAlloc_4809_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4808_;
            }
            15 => {
                v_ar_4824_ = lean_ctor_get(v_lean_4815_, 13);
                lean_inc_ref(v_ar_4824_);
                v___x_4825_ = l_Lake_compileStaticLib(
                    v___y_4722_,
                    v_oFiles_4723_,
                    v_ar_4824_,
                    v_shouldExport_4724_,
                    v_log_4816_,
                );
                if lean_obj_tag(v___x_4825_) == 0 {
                    v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
                    v_a_4827_ = lean_ctor_get(v___x_4825_, 1);
                    v_isSharedCheck_4837_ = (!lean_is_exclusive(v___x_4825_)) as u8;
                    if v_isSharedCheck_4837_ == 0 {
                        v___x_4829_ = v___x_4825_;
                        v_isShared_4830_ = v_isSharedCheck_4837_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_4827_);
                        lean_inc(v_a_4826_);
                        lean_dec(v___x_4825_);
                        v___x_4829_ = lean_box(0);
                        v_isShared_4830_ = v_isSharedCheck_4837_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_a_4838_ = lean_ctor_get(v___x_4825_, 0);
                    v_a_4839_ = lean_ctor_get(v___x_4825_, 1);
                    v_isSharedCheck_4849_ = (!lean_is_exclusive(v___x_4825_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4841_ = v___x_4825_;
                        v_isShared_4842_ = v_isSharedCheck_4849_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_4839_);
                        lean_inc(v_a_4838_);
                        lean_dec(v___x_4825_);
                        v___x_4841_ = lean_box(0);
                        v_isShared_4842_ = v_isSharedCheck_4849_;
                        state = 19;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_4823_ == 0 {
                    lean_ctor_set(v___x_4822_, 0, v_a_4827_);
                    v___x_4832_ = v___x_4822_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4827_);
                    lean_ctor_set(v_reuseFailAlloc_4836_, 1, v_trace_4819_);
                    lean_ctor_set(v_reuseFailAlloc_4836_, 2, v_buildTime_4820_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4836_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4817_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4836_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4818_,
                    );
                    v___x_4832_ = v_reuseFailAlloc_4836_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_4830_ == 0 {
                    lean_ctor_set(v___x_4829_, 1, v___x_4832_);
                    v___x_4834_ = v___x_4829_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4826_);
                    lean_ctor_set(v_reuseFailAlloc_4835_, 1, v___x_4832_);
                    v___x_4834_ = v_reuseFailAlloc_4835_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4834_;
            }
            19 => {
                if v_isShared_4823_ == 0 {
                    lean_ctor_set(v___x_4822_, 0, v_a_4839_);
                    v___x_4844_ = v___x_4822_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4839_);
                    lean_ctor_set(v_reuseFailAlloc_4848_, 1, v_trace_4819_);
                    lean_ctor_set(v_reuseFailAlloc_4848_, 2, v_buildTime_4820_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4848_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4817_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4848_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4818_,
                    );
                    v___x_4844_ = v_reuseFailAlloc_4848_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_4842_ == 0 {
                    lean_ctor_set(v___x_4841_, 1, v___x_4844_);
                    v___x_4846_ = v___x_4841_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4838_);
                    lean_ctor_set(v_reuseFailAlloc_4847_, 1, v___x_4844_);
                    v___x_4846_ = v_reuseFailAlloc_4847_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4846_;
            }
            22 => {
                v___x_4861_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1;
                v_log_4862_ = lean_ctor_get(v_a_4860_, 0);
                v_action_4863_ = lean_ctor_get_uint8(
                    v_a_4860_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4864_ = lean_ctor_get_uint8(
                    v_a_4860_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4865_ = lean_ctor_get(v_a_4860_, 1);
                v_buildTime_4866_ = lean_ctor_get(v_a_4860_, 2);
                v_isSharedCheck_4905_ = (!lean_is_exclusive(v_a_4860_)) as u8;
                if v_isSharedCheck_4905_ == 0 {
                    v___x_4868_ = v_a_4860_;
                    v_isShared_4869_ = v_isSharedCheck_4905_;
                    state = 23;
                    continue;
                } else {
                    lean_inc(v_buildTime_4866_);
                    lean_inc(v_trace_4865_);
                    lean_inc(v_log_4862_);
                    lean_dec(v_a_4860_);
                    v___x_4868_ = lean_box(0);
                    v_isShared_4869_ = v_isSharedCheck_4905_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_4870_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2;
                v___x_4871_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5;
                v___x_4872_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once), _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
                v___x_4873_ = lean_array_push(v___x_4872_, v___y_4722_);
                v___x_4874_ = lean_array_push(v___x_4873_, v___x_4871_);
                v___x_4875_ = lean_array_push(v___x_4874_, v___x_4858_);
                v___x_4876_ = lean_box(0);
                v___x_4877_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8;
                v___x_4878_ = 0;
                v___x_4879_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_4879_, 0, v___x_4861_);
                lean_ctor_set(v___x_4879_, 1, v___x_4870_);
                lean_ctor_set(v___x_4879_, 2, v___x_4875_);
                lean_ctor_set(v___x_4879_, 3, v___x_4876_);
                lean_ctor_set(v___x_4879_, 4, v___x_4877_);
                lean_ctor_set_uint8(
                    v___x_4879_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_4725_,
                );
                lean_ctor_set_uint8(
                    v___x_4879_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_4878_,
                );
                v___x_4880_ = l_Lake_proc(v___x_4879_, v___x_4878_, v_log_4862_);
                if lean_obj_tag(v___x_4880_) == 0 {
                    v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
                    v_a_4882_ = lean_ctor_get(v___x_4880_, 1);
                    v_isSharedCheck_4892_ = (!lean_is_exclusive(v___x_4880_)) as u8;
                    if v_isSharedCheck_4892_ == 0 {
                        v___x_4884_ = v___x_4880_;
                        v_isShared_4885_ = v_isSharedCheck_4892_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_4882_);
                        lean_inc(v_a_4881_);
                        lean_dec(v___x_4880_);
                        v___x_4884_ = lean_box(0);
                        v_isShared_4885_ = v_isSharedCheck_4892_;
                        state = 24;
                        continue;
                    }
                } else {
                    v_a_4893_ = lean_ctor_get(v___x_4880_, 0);
                    v_a_4894_ = lean_ctor_get(v___x_4880_, 1);
                    v_isSharedCheck_4904_ = (!lean_is_exclusive(v___x_4880_)) as u8;
                    if v_isSharedCheck_4904_ == 0 {
                        v___x_4896_ = v___x_4880_;
                        v_isShared_4897_ = v_isSharedCheck_4904_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_4894_);
                        lean_inc(v_a_4893_);
                        lean_dec(v___x_4880_);
                        v___x_4896_ = lean_box(0);
                        v_isShared_4897_ = v_isSharedCheck_4904_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_4869_ == 0 {
                    lean_ctor_set(v___x_4868_, 0, v_a_4882_);
                    v___x_4887_ = v___x_4868_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4882_);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 1, v_trace_4865_);
                    lean_ctor_set(v_reuseFailAlloc_4891_, 2, v_buildTime_4866_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4891_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4863_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4891_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4864_,
                    );
                    v___x_4887_ = v_reuseFailAlloc_4891_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_4885_ == 0 {
                    lean_ctor_set(v___x_4884_, 1, v___x_4887_);
                    v___x_4889_ = v___x_4884_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4881_);
                    lean_ctor_set(v_reuseFailAlloc_4890_, 1, v___x_4887_);
                    v___x_4889_ = v_reuseFailAlloc_4890_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4889_;
            }
            27 => {
                if v_isShared_4869_ == 0 {
                    lean_ctor_set(v___x_4868_, 0, v_a_4894_);
                    v___x_4899_ = v___x_4868_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4894_);
                    lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_trace_4865_);
                    lean_ctor_set(v_reuseFailAlloc_4903_, 2, v_buildTime_4866_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4903_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4863_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4903_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4864_,
                    );
                    v___x_4899_ = v_reuseFailAlloc_4903_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_4897_ == 0 {
                    lean_ctor_set(v___x_4896_, 1, v___x_4899_);
                    v___x_4901_ = v___x_4896_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4893_);
                    lean_ctor_set(v_reuseFailAlloc_4902_, 1, v___x_4899_);
                    v___x_4901_ = v_reuseFailAlloc_4902_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4901_;
            }
            30 => {
                if lean_obj_tag(v___y_4907_) == 0 {
                    v_a_4908_ = lean_ctor_get(v___y_4907_, 1);
                    lean_inc(v_a_4908_);
                    lean_dec_ref_known(v___y_4907_, 2);
                    v_a_4860_ = v_a_4908_;
                    state = 22;
                    continue;
                } else {
                    lean_dec_ref(v___x_4858_);
                    lean_dec_ref(v___y_4722_);
                    return v___y_4907_;
                }
            }
            31 => {
                v_a_4928_ = lean_ctor_get(v___x_4910_, 0);
                lean_inc(v_a_4928_);
                lean_dec_ref_known(v___x_4910_, 1);
                v___x_4929_ = lean_io_error_to_string(v_a_4928_);
                v___x_4930_ = 3;
                v___x_4931_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4931_, 0, v___x_4929_);
                lean_ctor_set_uint8(
                    v___x_4931_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4930_,
                );
                v___x_4932_ = lean_array_get_size(v_log_4851_);
                v___x_4933_ = lean_array_push(v_log_4851_, v___x_4931_);
                if v_isShared_4927_ == 0 {
                    lean_ctor_set(v___x_4926_, 0, v___x_4933_);
                    v___x_4935_ = v___x_4926_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4933_);
                    lean_ctor_set(v_reuseFailAlloc_4937_, 1, v_trace_4854_);
                    lean_ctor_set(v_reuseFailAlloc_4937_, 2, v_buildTime_4855_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4937_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4852_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4937_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4853_,
                    );
                    v___x_4935_ = v_reuseFailAlloc_4937_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_4936_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4936_, 0, v___x_4932_);
                lean_ctor_set(v___x_4936_, 1, v___x_4935_);
                return v___x_4936_;
            }
            33 => {
                v_a_4945_ = lean_ctor_get(v___x_4856_, 0);
                lean_inc(v_a_4945_);
                lean_dec_ref_known(v___x_4856_, 1);
                v___x_4946_ = lean_io_error_to_string(v_a_4945_);
                v___x_4947_ = 3;
                v___x_4948_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4948_, 0, v___x_4946_);
                lean_ctor_set_uint8(
                    v___x_4948_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4947_,
                );
                v___x_4949_ = lean_array_get_size(v_log_4851_);
                v___x_4950_ = lean_array_push(v_log_4851_, v___x_4948_);
                if v_isShared_4944_ == 0 {
                    lean_ctor_set(v___x_4943_, 0, v___x_4950_);
                    v___x_4952_ = v___x_4943_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4950_);
                    lean_ctor_set(v_reuseFailAlloc_4954_, 1, v_trace_4854_);
                    lean_ctor_set(v_reuseFailAlloc_4954_, 2, v_buildTime_4855_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4954_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4852_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4954_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4853_,
                    );
                    v___x_4952_ = v_reuseFailAlloc_4954_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v___x_4953_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4953_, 0, v___x_4949_);
                lean_ctor_set(v___x_4953_, 1, v___x_4952_);
                return v___x_4953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(
    mut v_bootstrap_4959_: *mut LeanObject,
    mut v___y_4960_: *mut LeanObject,
    mut v_oFiles_4961_: *mut LeanObject,
    mut v_shouldExport_4962_: *mut LeanObject,
    mut v___x_4963_: *mut LeanObject,
    mut v___x_4964_: *mut LeanObject,
    mut v___x_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
    mut v___y_4967_: *mut LeanObject,
    mut v___y_4968_: *mut LeanObject,
    mut v___y_4969_: *mut LeanObject,
    mut v___y_4970_: *mut LeanObject,
    mut v___y_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bootstrap_boxed_4973_: u8 = 0;
    let mut v_shouldExport_boxed_4974_: u8 = 0;
    let mut v___x_197474__boxed_4975_: u8 = 0;
    let mut v___x_197476__boxed_4976_: usize = 0;
    let mut v_res_4977_: *mut LeanObject = core::ptr::null_mut();
    v_bootstrap_boxed_4973_ = (lean_unbox(v_bootstrap_4959_) as u8);
    v_shouldExport_boxed_4974_ = (lean_unbox(v_shouldExport_4962_) as u8);
    v___x_197474__boxed_4975_ = (lean_unbox(v___x_4963_) as u8);
    v___x_197476__boxed_4976_ = lean_unbox_usize(v___x_4965_);
    lean_dec(v___x_4965_);
    v_res_4977_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(
        v_bootstrap_boxed_4973_,
        v___y_4960_,
        v_oFiles_4961_,
        v_shouldExport_boxed_4974_,
        v___x_197474__boxed_4975_,
        v___x_4964_,
        v___x_197476__boxed_4976_,
        v___y_4966_,
        v___y_4967_,
        v___y_4968_,
        v___y_4969_,
        v___y_4970_,
        v___y_4971_,
    );
    lean_dec_ref(v___y_4970_);
    lean_dec(v___y_4969_);
    lean_dec(v___y_4968_);
    lean_dec(v___y_4967_);
    return v_res_4977_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(
    mut v_bootstrap_4979_: u8,
    mut v___y_4980_: *mut LeanObject,
    mut v_shouldExport_4981_: u8,
    mut v___x_4982_: u8,
    mut v___x_4983_: *mut LeanObject,
    mut v___x_4984_: usize,
    mut v_oFiles_4985_: *mut LeanObject,
    mut v___y_4986_: *mut LeanObject,
    mut v___y_4987_: *mut LeanObject,
    mut v___y_4988_: *mut LeanObject,
    mut v___y_4989_: *mut LeanObject,
    mut v___y_4990_: *mut LeanObject,
    mut v___y_4991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5005_: u8 = 0;
    let mut v_path_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut v_a_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5015_: u8 = 0;
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4993_ = lean_box((v_bootstrap_4979_) as usize);
                v___x_4994_ = lean_box((v_shouldExport_4981_) as usize);
                v___x_4995_ = lean_box((v___x_4982_) as usize);
                v___x_4996_ = lean_box_usize(v___x_4984_);
                lean_inc_ref(v___y_4980_);
                v___y_4997_ = lean_alloc_closure(
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed
                        as *mut core::ffi::c_void,
                    14,
                    7,
                );
                lean_closure_set(v___y_4997_, 0, v___x_4993_);
                lean_closure_set(v___y_4997_, 1, v___y_4980_);
                lean_closure_set(v___y_4997_, 2, v_oFiles_4985_);
                lean_closure_set(v___y_4997_, 3, v___x_4994_);
                lean_closure_set(v___y_4997_, 4, v___x_4995_);
                lean_closure_set(v___y_4997_, 5, v___x_4983_);
                lean_closure_set(v___y_4997_, 6, v___x_4996_);
                v___x_4998_ = 0;
                v___x_4999_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0;
                v___x_5000_ = l_Lake_buildArtifactUnlessUpToDate(
                    v___y_4980_,
                    v___y_4997_,
                    v___x_4998_,
                    v___x_4999_,
                    v___x_4982_,
                    v___x_4998_,
                    v___x_4998_,
                    v___y_4986_,
                    v___y_4987_,
                    v___y_4988_,
                    v___y_4989_,
                    v___y_4990_,
                    v___y_4991_,
                );
                if lean_obj_tag(v___x_5000_) == 0 {
                    v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
                    v_a_5002_ = lean_ctor_get(v___x_5000_, 1);
                    v_isSharedCheck_5010_ = (!lean_is_exclusive(v___x_5000_)) as u8;
                    if v_isSharedCheck_5010_ == 0 {
                        v___x_5004_ = v___x_5000_;
                        v_isShared_5005_ = v_isSharedCheck_5010_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5002_);
                        lean_inc(v_a_5001_);
                        lean_dec(v___x_5000_);
                        v___x_5004_ = lean_box(0);
                        v_isShared_5005_ = v_isSharedCheck_5010_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5011_ = lean_ctor_get(v___x_5000_, 0);
                    v_a_5012_ = lean_ctor_get(v___x_5000_, 1);
                    v_isSharedCheck_5019_ = (!lean_is_exclusive(v___x_5000_)) as u8;
                    if v_isSharedCheck_5019_ == 0 {
                        v___x_5014_ = v___x_5000_;
                        v_isShared_5015_ = v_isSharedCheck_5019_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5012_);
                        lean_inc(v_a_5011_);
                        lean_dec(v___x_5000_);
                        v___x_5014_ = lean_box(0);
                        v_isShared_5015_ = v_isSharedCheck_5019_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_path_5006_ = lean_ctor_get(v_a_5001_, 1);
                lean_inc_ref(v_path_5006_);
                lean_dec(v_a_5001_);
                if v_isShared_5005_ == 0 {
                    lean_ctor_set(v___x_5004_, 0, v_path_5006_);
                    v___x_5008_ = v___x_5004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_path_5006_);
                    lean_ctor_set(v_reuseFailAlloc_5009_, 1, v_a_5002_);
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5008_;
            }
            3 => {
                if v_isShared_5015_ == 0 {
                    v___x_5017_ = v___x_5014_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5011_);
                    lean_ctor_set(v_reuseFailAlloc_5018_, 1, v_a_5012_);
                    v___x_5017_ = v_reuseFailAlloc_5018_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(
    mut v_bootstrap_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
    mut v_shouldExport_5022_: *mut LeanObject,
    mut v___x_5023_: *mut LeanObject,
    mut v___x_5024_: *mut LeanObject,
    mut v___x_5025_: *mut LeanObject,
    mut v_oFiles_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bootstrap_boxed_5034_: u8 = 0;
    let mut v_shouldExport_boxed_5035_: u8 = 0;
    let mut v___x_197899__boxed_5036_: u8 = 0;
    let mut v___x_197901__boxed_5037_: usize = 0;
    let mut v_res_5038_: *mut LeanObject = core::ptr::null_mut();
    v_bootstrap_boxed_5034_ = (lean_unbox(v_bootstrap_5020_) as u8);
    v_shouldExport_boxed_5035_ = (lean_unbox(v_shouldExport_5022_) as u8);
    v___x_197899__boxed_5036_ = (lean_unbox(v___x_5023_) as u8);
    v___x_197901__boxed_5037_ = lean_unbox_usize(v___x_5025_);
    lean_dec(v___x_5025_);
    v_res_5038_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(
        v_bootstrap_boxed_5034_,
        v___y_5021_,
        v_shouldExport_boxed_5035_,
        v___x_197899__boxed_5036_,
        v___x_5024_,
        v___x_197901__boxed_5037_,
        v_oFiles_5026_,
        v___y_5027_,
        v___y_5028_,
        v___y_5029_,
        v___y_5030_,
        v___y_5031_,
        v___y_5032_,
    );
    lean_dec_ref(v___y_5031_);
    lean_dec(v___y_5030_);
    lean_dec(v___y_5029_);
    lean_dec(v___y_5028_);
    return v_res_5038_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(
    mut v___x_5043_: *mut LeanObject,
    mut v___x_5044_: *mut LeanObject,
    mut v_config_5045_: *mut LeanObject,
    mut v_config_5046_: *mut LeanObject,
    mut v___x_5047_: *mut LeanObject,
    mut v___f_5048_: *mut LeanObject,
    mut v_shouldExport_5049_: u8,
    mut v___x_5050_: u8,
    mut v___x_5051_: *mut LeanObject,
    mut v___x_5052_: *mut LeanObject,
    mut v_dir_5053_: *mut LeanObject,
    mut v_self_5054_: *mut LeanObject,
    mut v___f_5055_: *mut LeanObject,
    mut v___y_5056_: *mut LeanObject,
    mut v___y_5057_: *mut LeanObject,
    mut v___y_5058_: *mut LeanObject,
    mut v___y_5059_: *mut LeanObject,
    mut v___y_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5066_: usize = 0;
    let mut v___y_5067_: u8 = 0;
    let mut v___y_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: u8 = 0;
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_5088_: u8 = 0;
    let mut v_buildDir_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5094_: usize = 0;
    let mut v___x_5095_: usize = 0;
    let mut v___x_197179__overap_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: u8 = 0;
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5123_: u8 = 0;
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5127_: u8 = 0;
    let mut v___y_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: u8 = 0;
    let mut v___x_5152_: usize = 0;
    let mut v___x_5153_: usize = 0;
    let mut v___x_197239__overap_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: usize = 0;
    let mut v___x_5157_: usize = 0;
    let mut v___x_197242__overap_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5168_: u8 = 0;
    let mut v_a_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5173_: u8 = 0;
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___y_5056_);
                lean_inc_ref(v___y_5060_);
                lean_inc(v___y_5059_);
                lean_inc(v___y_5058_);
                lean_inc(v___x_5044_);
                v___x_5141_ = lean_apply_7(
                    v___y_5056_,
                    v___x_5043_,
                    v___x_5044_,
                    v___y_5058_,
                    v___y_5059_,
                    v___y_5060_,
                    v___y_5061_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5141_) == 0 {
                    v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
                    lean_inc(v_a_5142_);
                    v_a_5143_ = lean_ctor_get(v___x_5141_, 1);
                    lean_inc(v_a_5143_);
                    lean_dec_ref_known(v___x_5141_, 2);
                    v___x_5144_ = l_Lake_Job_await___redArg(v_a_5142_, v_a_5143_);
                    if lean_obj_tag(v___x_5144_) == 0 {
                        v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
                        lean_inc(v_a_5145_);
                        v_a_5146_ = lean_ctor_get(v___x_5144_, 1);
                        lean_inc(v_a_5146_);
                        lean_dec_ref_known(v___x_5144_, 2);
                        v___x_5147_ = lean_unsigned_to_nat(0);
                        v___x_5148_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2;
                        v___x_5149_ = lean_array_get_size(v_a_5145_);
                        v___x_5150_ = lean_nat_dec_lt(v___x_5147_, v___x_5149_);
                        if v___x_5150_ == 0 {
                            lean_dec(v_a_5145_);
                            lean_dec_ref(v___f_5055_);
                            v_a_5084_ = v___x_5148_;
                            v_a_5085_ = v_a_5146_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5151_ = lean_nat_dec_le(v___x_5149_, v___x_5149_);
                            if v___x_5151_ == 0 {
                                if v___x_5150_ == 0 {
                                    lean_dec(v_a_5145_);
                                    lean_dec_ref(v___f_5055_);
                                    v_a_5084_ = v___x_5148_;
                                    v_a_5085_ = v_a_5146_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_5152_ = 0usize;
                                    v___x_5153_ = lean_usize_of_nat(v___x_5149_);
                                    lean_inc_ref(v___x_5047_);
                                    v___x_197239__overap_5154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5047_, v___f_5055_, v_a_5145_, v___x_5152_, v___x_5153_, v___x_5148_);
                                    lean_inc_ref(v___y_5060_);
                                    lean_inc(v___y_5059_);
                                    lean_inc(v___y_5058_);
                                    lean_inc(v___x_5044_);
                                    lean_inc_ref(v___y_5056_);
                                    v___x_5155_ = lean_apply_7(
                                        v___x_197239__overap_5154_,
                                        v___y_5056_,
                                        v___x_5044_,
                                        v___y_5058_,
                                        v___y_5059_,
                                        v___y_5060_,
                                        v_a_5146_,
                                        lean_box(0),
                                    );
                                    v___y_5129_ = v___x_5155_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___x_5156_ = 0usize;
                                v___x_5157_ = lean_usize_of_nat(v___x_5149_);
                                lean_inc_ref(v___x_5047_);
                                v___x_197242__overap_5158_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        lean_box(0),
                                        lean_box(0),
                                        lean_box(0),
                                        v___x_5047_,
                                        v___f_5055_,
                                        v_a_5145_,
                                        v___x_5156_,
                                        v___x_5157_,
                                        v___x_5148_,
                                    );
                                lean_inc_ref(v___y_5060_);
                                lean_inc(v___y_5059_);
                                lean_inc(v___y_5058_);
                                lean_inc(v___x_5044_);
                                lean_inc_ref(v___y_5056_);
                                v___x_5159_ = lean_apply_7(
                                    v___x_197242__overap_5158_,
                                    v___y_5056_,
                                    v___x_5044_,
                                    v___y_5058_,
                                    v___y_5059_,
                                    v___y_5060_,
                                    v_a_5146_,
                                    lean_box(0),
                                );
                                v___y_5129_ = v___x_5159_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_5056_);
                        lean_dec_ref(v___f_5055_);
                        lean_dec_ref(v_self_5054_);
                        lean_dec_ref(v_dir_5053_);
                        lean_dec(v___x_5052_);
                        lean_dec_ref(v___x_5051_);
                        lean_dec_ref(v___f_5048_);
                        lean_dec_ref(v___x_5047_);
                        lean_dec_ref(v_config_5045_);
                        lean_dec(v___x_5044_);
                        v_a_5160_ = lean_ctor_get(v___x_5144_, 0);
                        v_a_5161_ = lean_ctor_get(v___x_5144_, 1);
                        v_isSharedCheck_5168_ = (!lean_is_exclusive(v___x_5144_)) as u8;
                        if v_isSharedCheck_5168_ == 0 {
                            v___x_5163_ = v___x_5144_;
                            v_isShared_5164_ = v_isSharedCheck_5168_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5161_);
                            lean_inc(v_a_5160_);
                            lean_dec(v___x_5144_);
                            v___x_5163_ = lean_box(0);
                            v_isShared_5164_ = v_isSharedCheck_5168_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5056_);
                    lean_dec_ref(v___f_5055_);
                    lean_dec_ref(v_self_5054_);
                    lean_dec_ref(v_dir_5053_);
                    lean_dec(v___x_5052_);
                    lean_dec_ref(v___x_5051_);
                    lean_dec_ref(v___f_5048_);
                    lean_dec_ref(v___x_5047_);
                    lean_dec_ref(v_config_5045_);
                    lean_dec(v___x_5044_);
                    v_a_5169_ = lean_ctor_get(v___x_5141_, 0);
                    v_a_5170_ = lean_ctor_get(v___x_5141_, 1);
                    v_isSharedCheck_5177_ = (!lean_is_exclusive(v___x_5141_)) as u8;
                    if v_isSharedCheck_5177_ == 0 {
                        v___x_5172_ = v___x_5141_;
                        v_isShared_5173_ = v_isSharedCheck_5177_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5170_);
                        lean_inc(v_a_5169_);
                        lean_dec(v___x_5141_);
                        v___x_5172_ = lean_box(0);
                        v_isShared_5173_ = v_isSharedCheck_5177_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5070_ = lean_box((v___y_5067_) as usize);
                v___x_5071_ = lean_box((v_shouldExport_5049_) as usize);
                v___x_5072_ = lean_box((v___x_5050_) as usize);
                v___x_5073_ = lean_box_usize(v___y_5066_);
                v___f_5074_ = lean_alloc_closure(
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed
                        as *mut core::ffi::c_void,
                    14,
                    6,
                );
                lean_closure_set(v___f_5074_, 0, v___x_5070_);
                lean_closure_set(v___f_5074_, 1, v___y_5069_);
                lean_closure_set(v___f_5074_, 2, v___x_5071_);
                lean_closure_set(v___f_5074_, 3, v___x_5072_);
                lean_closure_set(v___f_5074_, 4, v___x_5051_);
                lean_closure_set(v___f_5074_, 5, v___x_5073_);
                v___x_5075_ = l_Array_append___redArg(v___y_5068_, v___y_5065_);
                lean_dec_ref(v___y_5065_);
                v___x_5076_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0;
                v___x_5077_ = l_Lake_Job_collectArray___redArg(v___x_5075_, v___x_5076_);
                lean_dec_ref(v___x_5075_);
                v___x_5078_ = lean_unsigned_to_nat(0);
                v___x_5079_ = 0;
                v___x_5080_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once), _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
                v___x_5081_ = l_Lake_Job_mapM___redArg(
                    v___x_5052_,
                    v___x_5077_,
                    v___f_5074_,
                    v___x_5078_,
                    v___x_5079_,
                    v___y_5056_,
                    v___x_5044_,
                    v___y_5058_,
                    v___y_5059_,
                    v___y_5060_,
                    v___x_5080_,
                );
                lean_dec(v___x_5044_);
                v___x_5082_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5082_, 0, v___x_5081_);
                lean_ctor_set(v___x_5082_, 1, v___y_5064_);
                return v___x_5082_;
            }
            2 => {
                v_toLeanConfig_5086_ = lean_ctor_get(v_config_5045_, 1);
                lean_inc_ref(v_toLeanConfig_5086_);
                v_toLeanConfig_5087_ = lean_ctor_get(v_config_5046_, 0);
                v_bootstrap_5088_ = lean_ctor_get_uint8(
                    v_config_5045_,
                    (core::mem::size_of::<*mut LeanObject>() * 27) as u32,
                );
                v_buildDir_5089_ = lean_ctor_get(v_config_5045_, 5);
                lean_inc_ref(v_buildDir_5089_);
                v_nativeLibDir_5090_ = lean_ctor_get(v_config_5045_, 7);
                lean_inc_ref(v_nativeLibDir_5090_);
                lean_dec_ref(v_config_5045_);
                v_moreLinkObjs_5091_ = lean_ctor_get(v_toLeanConfig_5086_, 6);
                lean_inc_ref(v_moreLinkObjs_5091_);
                lean_dec_ref(v_toLeanConfig_5086_);
                v_moreLinkObjs_5092_ = lean_ctor_get(v_toLeanConfig_5087_, 6);
                v___x_5093_ = l_Array_append___redArg(v_moreLinkObjs_5091_, v_moreLinkObjs_5092_);
                v_sz_5094_ = lean_array_size(v___x_5093_);
                v___x_5095_ = 0usize;
                v___x_197179__overap_5096_ =
                    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_5047_,
                        v___f_5048_,
                        v_sz_5094_,
                        v___x_5095_,
                        v___x_5093_,
                    );
                lean_inc_ref(v___y_5060_);
                lean_inc(v___y_5059_);
                lean_inc(v___y_5058_);
                lean_inc(v___x_5044_);
                lean_inc_ref(v___y_5056_);
                v___x_5097_ = lean_apply_7(
                    v___x_197179__overap_5096_,
                    v___y_5056_,
                    v___x_5044_,
                    v___y_5058_,
                    v___y_5059_,
                    v___y_5060_,
                    v_a_5085_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5097_) == 0 {
                    if v_shouldExport_5049_ == 0 {
                        v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
                        lean_inc(v_a_5098_);
                        v_a_5099_ = lean_ctor_get(v___x_5097_, 1);
                        lean_inc(v_a_5099_);
                        lean_dec_ref_known(v___x_5097_, 2);
                        v___x_5100_ = l_System_FilePath_normalize(v_buildDir_5089_);
                        v___x_5101_ = l_Lake_joinRelative(v_dir_5053_, v___x_5100_);
                        v___x_5102_ = l_System_FilePath_normalize(v_nativeLibDir_5090_);
                        v___x_5103_ = l_Lake_joinRelative(v___x_5101_, v___x_5102_);
                        v___x_5104_ = l_Lake_LeanLib_libName(v_self_5054_);
                        v___x_5105_ = l_Lake_nameToStaticLib(v___x_5104_, v_shouldExport_5049_);
                        v___x_5106_ = l_Lake_joinRelative(v___x_5103_, v___x_5105_);
                        v___y_5064_ = v_a_5099_;
                        v___y_5065_ = v_a_5098_;
                        v___y_5066_ = v___x_5095_;
                        v___y_5067_ = v_bootstrap_5088_;
                        v___y_5068_ = v_a_5084_;
                        v___y_5069_ = v___x_5106_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5107_ = lean_ctor_get(v___x_5097_, 0);
                        lean_inc(v_a_5107_);
                        v_a_5108_ = lean_ctor_get(v___x_5097_, 1);
                        lean_inc(v_a_5108_);
                        lean_dec_ref_known(v___x_5097_, 2);
                        v___x_5109_ = l_System_FilePath_normalize(v_buildDir_5089_);
                        v___x_5110_ = l_Lake_joinRelative(v_dir_5053_, v___x_5109_);
                        v___x_5111_ = l_System_FilePath_normalize(v_nativeLibDir_5090_);
                        v___x_5112_ = l_Lake_joinRelative(v___x_5110_, v___x_5111_);
                        v___x_5113_ = l_Lake_LeanLib_libName(v_self_5054_);
                        v___x_5114_ = 0;
                        v___x_5115_ = l_Lake_nameToStaticLib(v___x_5113_, v___x_5114_);
                        v___x_5116_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1;
                        v___x_5117_ = l_System_FilePath_addExtension(v___x_5115_, v___x_5116_);
                        v___x_5118_ = l_Lake_joinRelative(v___x_5112_, v___x_5117_);
                        v___y_5064_ = v_a_5108_;
                        v___y_5065_ = v_a_5107_;
                        v___y_5066_ = v___x_5095_;
                        v___y_5067_ = v_bootstrap_5088_;
                        v___y_5068_ = v_a_5084_;
                        v___y_5069_ = v___x_5118_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_nativeLibDir_5090_);
                    lean_dec_ref(v_buildDir_5089_);
                    lean_dec_ref(v_a_5084_);
                    lean_dec_ref(v___y_5056_);
                    lean_dec_ref(v_self_5054_);
                    lean_dec_ref(v_dir_5053_);
                    lean_dec(v___x_5052_);
                    lean_dec_ref(v___x_5051_);
                    lean_dec(v___x_5044_);
                    v_a_5119_ = lean_ctor_get(v___x_5097_, 0);
                    v_a_5120_ = lean_ctor_get(v___x_5097_, 1);
                    v_isSharedCheck_5127_ = (!lean_is_exclusive(v___x_5097_)) as u8;
                    if v_isSharedCheck_5127_ == 0 {
                        v___x_5122_ = v___x_5097_;
                        v_isShared_5123_ = v_isSharedCheck_5127_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5120_);
                        lean_inc(v_a_5119_);
                        lean_dec(v___x_5097_);
                        v___x_5122_ = lean_box(0);
                        v_isShared_5123_ = v_isSharedCheck_5127_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5123_ == 0 {
                    v___x_5125_ = v___x_5122_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5119_);
                    lean_ctor_set(v_reuseFailAlloc_5126_, 1, v_a_5120_);
                    v___x_5125_ = v_reuseFailAlloc_5126_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5125_;
            }
            5 => {
                if lean_obj_tag(v___y_5129_) == 0 {
                    v_a_5130_ = lean_ctor_get(v___y_5129_, 0);
                    lean_inc(v_a_5130_);
                    v_a_5131_ = lean_ctor_get(v___y_5129_, 1);
                    lean_inc(v_a_5131_);
                    lean_dec_ref_known(v___y_5129_, 2);
                    v_a_5084_ = v_a_5130_;
                    v_a_5085_ = v_a_5131_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v___y_5056_);
                    lean_dec_ref(v_self_5054_);
                    lean_dec_ref(v_dir_5053_);
                    lean_dec(v___x_5052_);
                    lean_dec_ref(v___x_5051_);
                    lean_dec_ref(v___f_5048_);
                    lean_dec_ref(v___x_5047_);
                    lean_dec_ref(v_config_5045_);
                    lean_dec(v___x_5044_);
                    v_a_5132_ = lean_ctor_get(v___y_5129_, 0);
                    v_a_5133_ = lean_ctor_get(v___y_5129_, 1);
                    v_isSharedCheck_5140_ = (!lean_is_exclusive(v___y_5129_)) as u8;
                    if v_isSharedCheck_5140_ == 0 {
                        v___x_5135_ = v___y_5129_;
                        v_isShared_5136_ = v_isSharedCheck_5140_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5133_);
                        lean_inc(v_a_5132_);
                        lean_dec(v___y_5129_);
                        v___x_5135_ = lean_box(0);
                        v_isShared_5136_ = v_isSharedCheck_5140_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5136_ == 0 {
                    v___x_5138_ = v___x_5135_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5132_);
                    lean_ctor_set(v_reuseFailAlloc_5139_, 1, v_a_5133_);
                    v___x_5138_ = v_reuseFailAlloc_5139_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5138_;
            }
            8 => {
                if v_isShared_5164_ == 0 {
                    v___x_5166_ = v___x_5163_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5160_);
                    lean_ctor_set(v_reuseFailAlloc_5167_, 1, v_a_5161_);
                    v___x_5166_ = v_reuseFailAlloc_5167_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5166_;
            }
            10 => {
                if v_isShared_5173_ == 0 {
                    v___x_5175_ = v___x_5172_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5176_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_a_5169_);
                    lean_ctor_set(v_reuseFailAlloc_5176_, 1, v_a_5170_);
                    v___x_5175_ = v_reuseFailAlloc_5176_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5178_: *mut LeanObject = *_args.add(0);
    let mut v___x_5179_: *mut LeanObject = *_args.add(1);
    let mut v_config_5180_: *mut LeanObject = *_args.add(2);
    let mut v_config_5181_: *mut LeanObject = *_args.add(3);
    let mut v___x_5182_: *mut LeanObject = *_args.add(4);
    let mut v___f_5183_: *mut LeanObject = *_args.add(5);
    let mut v_shouldExport_5184_: *mut LeanObject = *_args.add(6);
    let mut v___x_5185_: *mut LeanObject = *_args.add(7);
    let mut v___x_5186_: *mut LeanObject = *_args.add(8);
    let mut v___x_5187_: *mut LeanObject = *_args.add(9);
    let mut v_dir_5188_: *mut LeanObject = *_args.add(10);
    let mut v_self_5189_: *mut LeanObject = *_args.add(11);
    let mut v___f_5190_: *mut LeanObject = *_args.add(12);
    let mut v___y_5191_: *mut LeanObject = *_args.add(13);
    let mut v___y_5192_: *mut LeanObject = *_args.add(14);
    let mut v___y_5193_: *mut LeanObject = *_args.add(15);
    let mut v___y_5194_: *mut LeanObject = *_args.add(16);
    let mut v___y_5195_: *mut LeanObject = *_args.add(17);
    let mut v___y_5196_: *mut LeanObject = *_args.add(18);
    let mut v___y_5197_: *mut LeanObject = *_args.add(19);
    let mut v_shouldExport_boxed_5198_: u8 = 0;
    let mut v___x_198003__boxed_5199_: u8 = 0;
    let mut v_res_5200_: *mut LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_5198_ = (lean_unbox(v_shouldExport_5184_) as u8);
    v___x_198003__boxed_5199_ = (lean_unbox(v___x_5185_) as u8);
    v_res_5200_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(
        v___x_5178_,
        v___x_5179_,
        v_config_5180_,
        v_config_5181_,
        v___x_5182_,
        v___f_5183_,
        v_shouldExport_boxed_5198_,
        v___x_198003__boxed_5199_,
        v___x_5186_,
        v___x_5187_,
        v_dir_5188_,
        v_self_5189_,
        v___f_5190_,
        v___y_5191_,
        v___y_5192_,
        v___y_5193_,
        v___y_5194_,
        v___y_5195_,
        v___y_5196_,
    );
    lean_dec_ref(v___y_5195_);
    lean_dec(v___y_5194_);
    lean_dec(v___y_5193_);
    lean_dec(v___y_5192_);
    lean_dec(v_config_5181_);
    return v_res_5200_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(
    mut v_self_5204_: *mut LeanObject,
    mut v_shouldExport_5205_: u8,
    mut v_a_5206_: *mut LeanObject,
    mut v_a_5207_: *mut LeanObject,
    mut v_a_5208_: *mut LeanObject,
    mut v_a_5209_: *mut LeanObject,
    mut v_a_5210_: *mut LeanObject,
    mut v_a_5211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBuildConfig_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_registeredJobs_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_5233_: u8 = 0;
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: u8 = 0;
    let mut v___x_5238_: u8 = 0;
    let mut v___x_5239_: u8 = 0;
    let mut v___y_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5262_: u8 = 0;
    let mut v_task_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5267_: u8 = 0;
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: u8 = 0;
    let mut v_job_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut v_unused_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5286_: u8 = 0;
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5213_ = l_instMonadBaseIO;
                v_toApplicative_5214_ = lean_ctor_get(v___x_5213_, 0);
                v_toBind_5215_ = lean_ctor_get(v___x_5213_, 1);
                v_toFunctor_5216_ = lean_ctor_get(v_toApplicative_5214_, 0);
                v_toPure_5217_ = lean_ctor_get(v_toApplicative_5214_, 1);
                lean_inc_n(v_toBind_5215_, 3);
                lean_inc_n(v_toPure_5217_, 5);
                v___f_5218_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_5218_, 0, v_toPure_5217_);
                lean_closure_set(v___f_5218_, 1, v_toBind_5215_);
                v___f_5219_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_5219_, 0, v_toPure_5217_);
                lean_closure_set(v___f_5219_, 1, v_toBind_5215_);
                lean_inc_ref(v___f_5218_);
                v___f_5220_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_5220_, 0, v_toPure_5217_);
                lean_closure_set(v___f_5220_, 1, v___f_5218_);
                lean_inc_ref_n(v_toFunctor_5216_, 2);
                v___f_5221_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                lean_closure_set(v___f_5221_, 0, v_toFunctor_5216_);
                lean_closure_set(v___f_5221_, 1, v_toPure_5217_);
                lean_closure_set(v___f_5221_, 2, v_toBind_5215_);
                v___x_5222_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_5216_);
                v___f_5223_ = lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_5223_, 0, v_toPure_5217_);
                v___x_5224_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5224_, 0, v___x_5222_);
                lean_ctor_set(v___x_5224_, 1, v___f_5223_);
                lean_ctor_set(v___x_5224_, 2, v___f_5221_);
                lean_ctor_set(v___x_5224_, 3, v___f_5220_);
                lean_ctor_set(v___x_5224_, 4, v___f_5219_);
                v___x_5225_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5225_, 0, v___x_5224_);
                lean_ctor_set(v___x_5225_, 1, v___f_5218_);
                v___x_5226_ = l_ReaderT_instMonad___redArg(v___x_5225_);
                v___x_5227_ = l_StateRefT_x27_instMonad___redArg(v___x_5226_);
                v___x_5228_ = l_ReaderT_instMonad___redArg(v___x_5227_);
                v___x_5229_ = l_ReaderT_instMonad___redArg(v___x_5228_);
                lean_inc_ref(v___x_5229_);
                v___x_5230_ = l_Lake_EquipT_instMonad___redArg(v___x_5229_);
                v_toBuildConfig_5231_ = lean_ctor_get(v_a_5210_, 0);
                v_registeredJobs_5232_ = lean_ctor_get(v_a_5210_, 3);
                v_verbosity_5233_ = lean_ctor_get_uint8(
                    v_toBuildConfig_5231_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v___x_5234_ = l_Lake_instDataKindFilePath;
                v___x_5235_ = lean_box((v_shouldExport_5205_) as usize);
                lean_inc_ref(v___x_5230_);
                v___f_5236_ = lean_alloc_closure(
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed
                        as *mut core::ffi::c_void,
                    11,
                    2,
                );
                lean_closure_set(v___f_5236_, 0, v___x_5235_);
                lean_closure_set(v___f_5236_, 1, v___x_5230_);
                v___x_5237_ = 2;
                v___x_5238_ = l_Lake_instDecidableEqVerbosity(v_verbosity_5233_, v___x_5237_);
                v___x_5239_ = 1;
                if v___x_5238_ == 0 {
                    v___x_5287_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0;
                    v___y_5241_ = v___x_5287_;
                    state = 1;
                    continue;
                } else {
                    if v_shouldExport_5205_ == 0 {
                        v___x_5288_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1;
                        v___y_5241_ = v___x_5288_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5289_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2;
                        v___y_5241_ = v___x_5289_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pkg_5242_ = lean_ctor_get(v_self_5204_, 0);
                v_name_5243_ = lean_ctor_get(v_self_5204_, 1);
                lean_inc_n(v_name_5243_, 2);
                v_config_5244_ = lean_ctor_get(v_self_5204_, 2);
                lean_inc(v_config_5244_);
                v_keyName_5245_ = lean_ctor_get(v_pkg_5242_, 2);
                v_dir_5246_ = lean_ctor_get(v_pkg_5242_, 4);
                lean_inc_ref(v_dir_5246_);
                v_config_5247_ = lean_ctor_get(v_pkg_5242_, 6);
                lean_inc_ref(v_config_5247_);
                lean_inc_ref_n(v_pkg_5242_, 2);
                v___f_5248_ = lean_alloc_closure(
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed
                        as *mut core::ffi::c_void,
                    10,
                    2,
                );
                lean_closure_set(v___f_5248_, 0, v___x_5234_);
                lean_closure_set(v___f_5248_, 1, v_pkg_5242_);
                v___x_5249_ = l_Lake_LeanLib_modulesFacet;
                lean_inc(v_keyName_5245_);
                v___x_5250_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_5250_, 0, v_keyName_5245_);
                lean_ctor_set(v___x_5250_, 1, v_name_5243_);
                v___x_5251_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
                lean_inc_ref(v_self_5204_);
                v___x_5252_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_5252_, 0, v___x_5250_);
                lean_ctor_set(v___x_5252_, 1, v___x_5251_);
                lean_ctor_set(v___x_5252_, 2, v_self_5204_);
                lean_ctor_set(v___x_5252_, 3, v___x_5249_);
                v___x_5253_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5253_, 0, v_pkg_5242_);
                v___x_5254_ = lean_box((v_shouldExport_5205_) as usize);
                v___x_5255_ = lean_box((v___x_5239_) as usize);
                v___f_5256_ = lean_alloc_closure(
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed
                        as *mut core::ffi::c_void,
                    20,
                    13,
                );
                lean_closure_set(v___f_5256_, 0, v___x_5252_);
                lean_closure_set(v___f_5256_, 1, v___x_5253_);
                lean_closure_set(v___f_5256_, 2, v_config_5247_);
                lean_closure_set(v___f_5256_, 3, v_config_5244_);
                lean_closure_set(v___f_5256_, 4, v___x_5230_);
                lean_closure_set(v___f_5256_, 5, v___f_5248_);
                lean_closure_set(v___f_5256_, 6, v___x_5254_);
                lean_closure_set(v___f_5256_, 7, v___x_5255_);
                lean_closure_set(v___f_5256_, 8, v___x_5229_);
                lean_closure_set(v___f_5256_, 9, v___x_5234_);
                lean_closure_set(v___f_5256_, 10, v_dir_5246_);
                lean_closure_set(v___f_5256_, 11, v_self_5204_);
                lean_closure_set(v___f_5256_, 12, v___f_5236_);
                v___x_5257_ = l_Lake_ensureJob___redArg(
                    v___x_5234_,
                    v___f_5256_,
                    v_a_5206_,
                    v_a_5207_,
                    v_a_5208_,
                    v_a_5209_,
                    v_a_5210_,
                    v_a_5211_,
                );
                if lean_obj_tag(v___x_5257_) == 0 {
                    v_a_5258_ = lean_ctor_get(v___x_5257_, 0);
                    v_a_5259_ = lean_ctor_get(v___x_5257_, 1);
                    v_isSharedCheck_5286_ = (!lean_is_exclusive(v___x_5257_)) as u8;
                    if v_isSharedCheck_5286_ == 0 {
                        v___x_5261_ = v___x_5257_;
                        v_isShared_5262_ = v_isSharedCheck_5286_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5259_);
                        lean_inc(v_a_5258_);
                        lean_dec(v___x_5257_);
                        v___x_5261_ = lean_box(0);
                        v_isShared_5262_ = v_isSharedCheck_5286_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_name_5243_);
                    return v___x_5257_;
                }
            }
            2 => {
                v_task_5263_ = lean_ctor_get(v_a_5258_, 0);
                v_kind_5264_ = lean_ctor_get(v_a_5258_, 1);
                v_isSharedCheck_5284_ = (!lean_is_exclusive(v_a_5258_)) as u8;
                if v_isSharedCheck_5284_ == 0 {
                    v_unused_5285_ = lean_ctor_get(v_a_5258_, 2);
                    lean_dec(v_unused_5285_);
                    v___x_5266_ = v_a_5258_;
                    v_isShared_5267_ = v_isSharedCheck_5284_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_kind_5264_);
                    lean_inc(v_task_5263_);
                    lean_dec(v_a_5258_);
                    v___x_5266_ = lean_box(0);
                    v_isShared_5267_ = v_isSharedCheck_5284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5268_ = lean_st_ref_take(v_registeredJobs_5232_);
                v___x_5269_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_5243_,
                    v___x_5239_,
                );
                v___x_5270_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0;
                v___x_5271_ = lean_string_append(v___x_5269_, v___x_5270_);
                v___x_5272_ = lean_string_append(v___x_5271_, v___y_5241_);
                v___x_5273_ = 0;
                if v_isShared_5267_ == 0 {
                    lean_ctor_set(v___x_5266_, 2, v___x_5272_);
                    v_job_5275_ = v___x_5266_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_task_5263_);
                    lean_ctor_set(v_reuseFailAlloc_5283_, 1, v_kind_5264_);
                    lean_ctor_set(v_reuseFailAlloc_5283_, 2, v___x_5272_);
                    v_job_5275_ = v_reuseFailAlloc_5283_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v_job_5275_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5273_,
                );
                lean_inc_ref(v_job_5275_);
                v___x_5276_ = l_Lake_Job_toOpaque___redArg(v_job_5275_);
                v___x_5277_ = lean_array_push(v___x_5268_, v___x_5276_);
                v___x_5278_ = lean_st_ref_set(v_registeredJobs_5232_, v___x_5277_);
                v___x_5279_ = l_Lake_Job_renew___redArg(v_job_5275_);
                if v_isShared_5262_ == 0 {
                    lean_ctor_set(v___x_5261_, 0, v___x_5279_);
                    v___x_5281_ = v___x_5261_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5279_);
                    lean_ctor_set(v_reuseFailAlloc_5282_, 1, v_a_5259_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(
    mut v_self_5290_: *mut LeanObject,
    mut v_shouldExport_5291_: *mut LeanObject,
    mut v_a_5292_: *mut LeanObject,
    mut v_a_5293_: *mut LeanObject,
    mut v_a_5294_: *mut LeanObject,
    mut v_a_5295_: *mut LeanObject,
    mut v_a_5296_: *mut LeanObject,
    mut v_a_5297_: *mut LeanObject,
    mut v_a_5298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldExport_boxed_5299_: u8 = 0;
    let mut v_res_5300_: *mut LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_5299_ = (lean_unbox(v_shouldExport_5291_) as u8);
    v_res_5300_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(
        v_self_5290_,
        v_shouldExport_boxed_5299_,
        v_a_5292_,
        v_a_5293_,
        v_a_5294_,
        v_a_5295_,
        v_a_5296_,
        v_a_5297_,
    );
    lean_dec_ref(v_a_5296_);
    lean_dec(v_a_5295_);
    lean_dec(v_a_5294_);
    lean_dec(v_a_5293_);
    return v_res_5300_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(
    mut v_fmt_5301_: u8,
    mut v_a_5302_: *mut LeanObject,
) -> *mut LeanObject {
    if v_fmt_5301_ == 0 {
        return v_a_5302_;
    } else {
        let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
        v___x_5303_ = l_Lake_mkRelPathString(v_a_5302_);
        v___x_5304_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_5304_, 0, v___x_5303_);
        v___x_5305_ = l_Lean_Json_compress(v___x_5304_);
        return v___x_5305_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(
    mut v_fmt_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_5308_: u8 = 0;
    let mut v_res_5309_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_5308_ = (lean_unbox(v_fmt_5306_) as u8);
    v_res_5309_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(
        v_fmt_boxed_5308_,
        v_a_5307_,
    );
    return v_res_5309_;
}
pub unsafe fn _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_5312_: u8 = 0;
    let mut v_name_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    v___x_5312_ = 1;
    v_name_5313_ = l_Lake_instDataKindFilePath;
    v___x_5314_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_5313_,
        v___x_5312_,
    );
    return v___x_5314_;
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(
    mut v_defaultPkg_5318_: *mut LeanObject,
    mut v_self_5319_: *mut LeanObject,
    mut v_a_5320_: *mut LeanObject,
    mut v_a_5321_: *mut LeanObject,
    mut v_a_5322_: *mut LeanObject,
    mut v_a_5323_: *mut LeanObject,
    mut v_a_5324_: *mut LeanObject,
    mut v_a_5325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5327_: u8 = 0;
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v_a_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5337_: u8 = 0;
    let mut v_kind_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: u8 = 0;
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: u8 = 0;
    let mut v___x_5360_: u8 = 0;
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5369_: u8 = 0;
    let mut v_unused_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5371_: u8 = 0;
    let mut v_unused_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5377_: u8 = 0;
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5327_ = 1;
                lean_inc_ref_n(v_self_5319_, 2);
                v___x_5328_ =
                    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
                        v_defaultPkg_5318_,
                        v_self_5319_,
                        v_self_5319_,
                        v___x_5327_,
                        v_a_5320_,
                        v_a_5321_,
                        v_a_5322_,
                        v_a_5323_,
                        v_a_5324_,
                        v_a_5325_,
                    );
                if lean_obj_tag(v___x_5328_) == 0 {
                    v_a_5329_ = lean_ctor_get(v___x_5328_, 0);
                    lean_inc(v_a_5329_);
                    v_snd_5330_ = lean_ctor_get(v_a_5329_, 1);
                    v_isSharedCheck_5371_ = (!lean_is_exclusive(v_a_5329_)) as u8;
                    if v_isSharedCheck_5371_ == 0 {
                        v_unused_5372_ = lean_ctor_get(v_a_5329_, 0);
                        lean_dec(v_unused_5372_);
                        v___x_5332_ = v_a_5329_;
                        v_isShared_5333_ = v_isSharedCheck_5371_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5330_);
                        lean_dec(v_a_5329_);
                        v___x_5332_ = lean_box(0);
                        v_isShared_5333_ = v_isSharedCheck_5371_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_self_5319_);
                    v_a_5373_ = lean_ctor_get(v___x_5328_, 0);
                    v_a_5374_ = lean_ctor_get(v___x_5328_, 1);
                    v_isSharedCheck_5381_ = (!lean_is_exclusive(v___x_5328_)) as u8;
                    if v_isSharedCheck_5381_ == 0 {
                        v___x_5376_ = v___x_5328_;
                        v_isShared_5377_ = v_isSharedCheck_5381_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5374_);
                        lean_inc(v_a_5373_);
                        lean_dec(v___x_5328_);
                        v___x_5376_ = lean_box(0);
                        v_isShared_5377_ = v_isSharedCheck_5381_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5334_ = lean_ctor_get(v___x_5328_, 1);
                v_isSharedCheck_5369_ = (!lean_is_exclusive(v___x_5328_)) as u8;
                if v_isSharedCheck_5369_ == 0 {
                    v_unused_5370_ = lean_ctor_get(v___x_5328_, 0);
                    lean_dec(v_unused_5370_);
                    v___x_5336_ = v___x_5328_;
                    v_isShared_5337_ = v_isSharedCheck_5369_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_5334_);
                    lean_dec(v___x_5328_);
                    v___x_5336_ = lean_box(0);
                    v_isShared_5337_ = v_isSharedCheck_5369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_kind_5338_ = lean_ctor_get(v_snd_5330_, 1);
                v_name_5339_ = l_Lake_instDataKindFilePath;
                v___x_5359_ = lean_name_eq(v_kind_5338_, v_name_5339_);
                if v___x_5359_ == 0 {
                    lean_inc(v_kind_5338_);
                    lean_del_object(v___x_5332_);
                    lean_dec(v_snd_5330_);
                    v___x_5360_ = l_Lean_Name_isAnonymous(v_kind_5338_);
                    if v___x_5360_ == 0 {
                        v___x_5361_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4;
                        v___x_5362_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_5338_,
                                v___x_5327_,
                            );
                        v___x_5363_ = lean_string_append(v___x_5361_, v___x_5362_);
                        lean_dec_ref(v___x_5362_);
                        v___x_5364_ = lean_string_append(v___x_5363_, v___x_5361_);
                        v___y_5341_ = v___x_5364_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_kind_5338_);
                        v___x_5365_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5;
                        v___y_5341_ = v___x_5365_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5336_);
                    lean_dec_ref(v_self_5319_);
                    if v_isShared_5333_ == 0 {
                        lean_ctor_set(v___x_5332_, 1, v_a_5334_);
                        lean_ctor_set(v___x_5332_, 0, v_snd_5330_);
                        v___x_5367_ = v___x_5332_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_snd_5330_);
                        lean_ctor_set(v_reuseFailAlloc_5368_, 1, v_a_5334_);
                        v___x_5367_ = v_reuseFailAlloc_5368_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5342_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0;
                v___x_5343_ = l_Lake_PartialBuildKey_toString(v_self_5319_);
                v___x_5344_ = lean_string_append(v___x_5342_, v___x_5343_);
                lean_dec_ref(v___x_5343_);
                v___x_5345_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1;
                v___x_5346_ = lean_string_append(v___x_5344_, v___x_5345_);
                v___x_5347_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once), _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
                v___x_5348_ = lean_string_append(v___x_5346_, v___x_5347_);
                v___x_5349_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3;
                v___x_5350_ = lean_string_append(v___x_5348_, v___x_5349_);
                v___x_5351_ = lean_string_append(v___x_5350_, v___y_5341_);
                lean_dec_ref(v___y_5341_);
                v___x_5352_ = 3;
                v___x_5353_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5353_, 0, v___x_5351_);
                lean_ctor_set_uint8(
                    v___x_5353_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5352_,
                );
                v___x_5354_ = lean_array_get_size(v_a_5334_);
                v___x_5355_ = lean_array_push(v_a_5334_, v___x_5353_);
                if v_isShared_5337_ == 0 {
                    lean_ctor_set_tag(v___x_5336_, 1);
                    lean_ctor_set(v___x_5336_, 1, v___x_5355_);
                    lean_ctor_set(v___x_5336_, 0, v___x_5354_);
                    v___x_5357_ = v___x_5336_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5358_, 0, v___x_5354_);
                    lean_ctor_set(v_reuseFailAlloc_5358_, 1, v___x_5355_);
                    v___x_5357_ = v_reuseFailAlloc_5358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5357_;
            }
            5 => {
                return v___x_5367_;
            }
            6 => {
                if v_isShared_5377_ == 0 {
                    v___x_5379_ = v___x_5376_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5373_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 1, v_a_5374_);
                    v___x_5379_ = v_reuseFailAlloc_5380_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(
    mut v_defaultPkg_5382_: *mut LeanObject,
    mut v_self_5383_: *mut LeanObject,
    mut v_a_5384_: *mut LeanObject,
    mut v_a_5385_: *mut LeanObject,
    mut v_a_5386_: *mut LeanObject,
    mut v_a_5387_: *mut LeanObject,
    mut v_a_5388_: *mut LeanObject,
    mut v_a_5389_: *mut LeanObject,
    mut v_a_5390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5391_: *mut LeanObject = core::ptr::null_mut();
    v_res_5391_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_5382_, v_self_5383_, v_a_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_);
    lean_dec_ref(v_a_5388_);
    lean_dec(v_a_5387_);
    lean_dec(v_a_5386_);
    lean_dec(v_a_5385_);
    return v_res_5391_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(
    mut v___x_5392_: *mut LeanObject,
    mut v_sz_5393_: usize,
    mut v_i_5394_: usize,
    mut v_bs_5395_: *mut LeanObject,
    mut v___y_5396_: *mut LeanObject,
    mut v___y_5397_: *mut LeanObject,
    mut v___y_5398_: *mut LeanObject,
    mut v___y_5399_: *mut LeanObject,
    mut v___y_5400_: *mut LeanObject,
    mut v___y_5401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5403_: u8 = 0;
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: usize = 0;
    let mut v___x_5412_: usize = 0;
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5419_: u8 = 0;
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5403_ = lean_usize_dec_lt(v_i_5394_, v_sz_5393_);
                if v___x_5403_ == 0 {
                    lean_dec_ref(v___y_5396_);
                    lean_dec_ref(v___x_5392_);
                    v___x_5404_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5404_, 0, v_bs_5395_);
                    lean_ctor_set(v___x_5404_, 1, v___y_5401_);
                    return v___x_5404_;
                } else {
                    v_v_5405_ = lean_array_uget_borrowed(v_bs_5395_, v_i_5394_);
                    lean_inc_ref(v___y_5396_);
                    lean_inc(v_v_5405_);
                    lean_inc_ref(v___x_5392_);
                    v___x_5406_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_5392_, v_v_5405_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
                    if lean_obj_tag(v___x_5406_) == 0 {
                        v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
                        lean_inc(v_a_5407_);
                        v_a_5408_ = lean_ctor_get(v___x_5406_, 1);
                        lean_inc(v_a_5408_);
                        lean_dec_ref_known(v___x_5406_, 2);
                        v___x_5409_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5410_ = lean_array_uset(v_bs_5395_, v_i_5394_, v___x_5409_);
                        v___x_5411_ = 1usize;
                        v___x_5412_ = lean_usize_add(v_i_5394_, v___x_5411_);
                        v___x_5413_ = lean_array_uset(v_bs_x27_5410_, v_i_5394_, v_a_5407_);
                        v_i_5394_ = v___x_5412_;
                        v_bs_5395_ = v___x_5413_;
                        v___y_5401_ = v_a_5408_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_5396_);
                        lean_dec_ref(v_bs_5395_);
                        lean_dec_ref(v___x_5392_);
                        v_a_5415_ = lean_ctor_get(v___x_5406_, 0);
                        v_a_5416_ = lean_ctor_get(v___x_5406_, 1);
                        v_isSharedCheck_5423_ = (!lean_is_exclusive(v___x_5406_)) as u8;
                        if v_isSharedCheck_5423_ == 0 {
                            v___x_5418_ = v___x_5406_;
                            v_isShared_5419_ = v_isSharedCheck_5423_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5416_);
                            lean_inc(v_a_5415_);
                            lean_dec(v___x_5406_);
                            v___x_5418_ = lean_box(0);
                            v_isShared_5419_ = v_isSharedCheck_5423_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5419_ == 0 {
                    v___x_5421_ = v___x_5418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5415_);
                    lean_ctor_set(v_reuseFailAlloc_5422_, 1, v_a_5416_);
                    v___x_5421_ = v_reuseFailAlloc_5422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(
    mut v___x_5424_: *mut LeanObject,
    mut v_sz_5425_: *mut LeanObject,
    mut v_i_5426_: *mut LeanObject,
    mut v_bs_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5435_: usize = 0;
    let mut v_i_boxed_5436_: usize = 0;
    let mut v_res_5437_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5435_ = lean_unbox_usize(v_sz_5425_);
    lean_dec(v_sz_5425_);
    v_i_boxed_5436_ = lean_unbox_usize(v_i_5426_);
    lean_dec(v_i_5426_);
    v_res_5437_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_5424_, v_sz_boxed_5435_, v_i_boxed_5436_, v_bs_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
    lean_dec_ref(v___y_5432_);
    lean_dec(v___y_5431_);
    lean_dec(v___y_5430_);
    lean_dec(v___y_5429_);
    return v_res_5437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(
    mut v_a_5438_: *mut LeanObject,
    mut v_as_5439_: *mut LeanObject,
    mut v_i_5440_: usize,
    mut v_stop_5441_: usize,
    mut v_b_5442_: *mut LeanObject,
    mut v___y_5443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5445_: u8 = 0;
    let mut v_log_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5447_: u8 = 0;
    let mut v_wantsRebuild_5448_: u8 = 0;
    let mut v_trace_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: usize = 0;
    let mut v___x_5457_: usize = 0;
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5461_: u8 = 0;
    let mut v_a_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: u8 = 0;
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5472_: u8 = 0;
    let mut v_unused_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5445_ = lean_usize_dec_eq(v_i_5440_, v_stop_5441_);
                if v___x_5445_ == 0 {
                    v_log_5446_ = lean_ctor_get(v___y_5443_, 0);
                    v_action_5447_ = lean_ctor_get_uint8(
                        v___y_5443_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_5448_ = lean_ctor_get_uint8(
                        v___y_5443_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_5449_ = lean_ctor_get(v___y_5443_, 1);
                    v_buildTime_5450_ = lean_ctor_get(v___y_5443_, 2);
                    v___x_5451_ = lean_array_uget_borrowed(v_as_5439_, v_i_5440_);
                    v___x_5452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0;
                    lean_inc(v___x_5451_);
                    v___x_5453_ = lean_string_append(v___x_5451_, v___x_5452_);
                    v___x_5454_ = lean_io_prim_handle_put_str(v_a_5438_, v___x_5453_);
                    lean_dec_ref(v___x_5453_);
                    if lean_obj_tag(v___x_5454_) == 0 {
                        v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
                        lean_inc(v_a_5455_);
                        lean_dec_ref_known(v___x_5454_, 1);
                        v___x_5456_ = 1usize;
                        v___x_5457_ = lean_usize_add(v_i_5440_, v___x_5456_);
                        v_i_5440_ = v___x_5457_;
                        v_b_5442_ = v_a_5455_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_buildTime_5450_);
                        lean_inc_ref(v_trace_5449_);
                        lean_inc_ref(v_log_5446_);
                        v_isSharedCheck_5472_ = (!lean_is_exclusive(v___y_5443_)) as u8;
                        if v_isSharedCheck_5472_ == 0 {
                            v_unused_5473_ = lean_ctor_get(v___y_5443_, 2);
                            lean_dec(v_unused_5473_);
                            v_unused_5474_ = lean_ctor_get(v___y_5443_, 1);
                            lean_dec(v_unused_5474_);
                            v_unused_5475_ = lean_ctor_get(v___y_5443_, 0);
                            lean_dec(v_unused_5475_);
                            v___x_5460_ = v___y_5443_;
                            v_isShared_5461_ = v_isSharedCheck_5472_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___y_5443_);
                            v___x_5460_ = lean_box(0);
                            v_isShared_5461_ = v_isSharedCheck_5472_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_5476_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5476_, 0, v_b_5442_);
                    lean_ctor_set(v___x_5476_, 1, v___y_5443_);
                    return v___x_5476_;
                }
            }
            1 => {
                v_a_5462_ = lean_ctor_get(v___x_5454_, 0);
                lean_inc(v_a_5462_);
                lean_dec_ref_known(v___x_5454_, 1);
                v___x_5463_ = lean_io_error_to_string(v_a_5462_);
                v___x_5464_ = 3;
                v___x_5465_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5465_, 0, v___x_5463_);
                lean_ctor_set_uint8(
                    v___x_5465_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5464_,
                );
                v___x_5466_ = lean_array_get_size(v_log_5446_);
                v___x_5467_ = lean_array_push(v_log_5446_, v___x_5465_);
                if v_isShared_5461_ == 0 {
                    lean_ctor_set(v___x_5460_, 0, v___x_5467_);
                    v___x_5469_ = v___x_5460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5471_, 0, v___x_5467_);
                    lean_ctor_set(v_reuseFailAlloc_5471_, 1, v_trace_5449_);
                    lean_ctor_set(v_reuseFailAlloc_5471_, 2, v_buildTime_5450_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5471_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5447_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5471_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5448_,
                    );
                    v___x_5469_ = v_reuseFailAlloc_5471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5470_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5470_, 0, v___x_5466_);
                lean_ctor_set(v___x_5470_, 1, v___x_5469_);
                return v___x_5470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(
    mut v_a_5477_: *mut LeanObject,
    mut v_as_5478_: *mut LeanObject,
    mut v_i_5479_: *mut LeanObject,
    mut v_stop_5480_: *mut LeanObject,
    mut v_b_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5484_: usize = 0;
    let mut v_stop_boxed_5485_: usize = 0;
    let mut v_res_5486_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5484_ = lean_unbox_usize(v_i_5479_);
    lean_dec(v_i_5479_);
    v_stop_boxed_5485_ = lean_unbox_usize(v_stop_5480_);
    lean_dec(v_stop_5480_);
    v_res_5486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_5477_, v_as_5478_, v_i_boxed_5484_, v_stop_boxed_5485_, v_b_5481_, v___y_5482_);
    lean_dec_ref(v_as_5478_);
    lean_dec(v_a_5477_);
    return v_res_5486_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(
    mut v_bootstrap_5487_: u8,
    mut v___y_5488_: *mut LeanObject,
    mut v_oFiles_5489_: *mut LeanObject,
    mut v_shouldExport_5490_: u8,
    mut v___x_5491_: u8,
    mut v___x_5492_: usize,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
    mut v___y_5497_: *mut LeanObject,
    mut v___y_5498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5504_: u8 = 0;
    let mut v_wantsRebuild_5505_: u8 = 0;
    let mut v_trace_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v_ar_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5517_: u8 = 0;
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5524_: u8 = 0;
    let mut v_a_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5529_: u8 = 0;
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_isSharedCheck_5537_: u8 = 0;
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: u8 = 0;
    let mut v_toContext_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5544_: u8 = 0;
    let mut v_wantsRebuild_5545_: u8 = 0;
    let mut v_trace_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v_ar_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5557_: u8 = 0;
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5564_: u8 = 0;
    let mut v_a_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5569_: u8 = 0;
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5576_: u8 = 0;
    let mut v_isSharedCheck_5577_: u8 = 0;
    let mut v_toContext_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5582_: u8 = 0;
    let mut v_wantsRebuild_5583_: u8 = 0;
    let mut v_trace_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5588_: u8 = 0;
    let mut v_ar_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_a_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5607_: u8 = 0;
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5614_: u8 = 0;
    let mut v_isSharedCheck_5615_: u8 = 0;
    let mut v_log_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5617_: u8 = 0;
    let mut v_wantsRebuild_5618_: u8 = 0;
    let mut v_trace_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5628_: u8 = 0;
    let mut v_wantsRebuild_5629_: u8 = 0;
    let mut v_trace_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5634_: u8 = 0;
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: u8 = 0;
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5652_: u8 = 0;
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5659_: u8 = 0;
    let mut v_a_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5664_: u8 = 0;
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5671_: u8 = 0;
    let mut v_isSharedCheck_5672_: u8 = 0;
    let mut v___y_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: u8 = 0;
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: u8 = 0;
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: u8 = 0;
    let mut v___x_5684_: usize = 0;
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: usize = 0;
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5690_: u8 = 0;
    let mut v_a_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: u8 = 0;
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5701_: u8 = 0;
    let mut v_unused_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5707_: u8 = 0;
    let mut v_a_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: u8 = 0;
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5718_: u8 = 0;
    let mut v_unused_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_bootstrap_5487_ == 0 {
                    v_toContext_5500_ = lean_ctor_get(v___y_5497_, 1);
                    v_lakeEnv_5501_ = lean_ctor_get(v_toContext_5500_, 0);
                    v_lean_5502_ = lean_ctor_get(v_lakeEnv_5501_, 1);
                    v_log_5503_ = lean_ctor_get(v___y_5498_, 0);
                    v_action_5504_ = lean_ctor_get_uint8(
                        v___y_5498_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_5505_ = lean_ctor_get_uint8(
                        v___y_5498_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_5506_ = lean_ctor_get(v___y_5498_, 1);
                    v_buildTime_5507_ = lean_ctor_get(v___y_5498_, 2);
                    v_isSharedCheck_5537_ = (!lean_is_exclusive(v___y_5498_)) as u8;
                    if v_isSharedCheck_5537_ == 0 {
                        v___x_5509_ = v___y_5498_;
                        v_isShared_5510_ = v_isSharedCheck_5537_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_buildTime_5507_);
                        lean_inc(v_trace_5506_);
                        lean_inc(v_log_5503_);
                        lean_dec(v___y_5498_);
                        v___x_5509_ = lean_box(0);
                        v_isShared_5510_ = v_isSharedCheck_5537_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5538_ = l_System_Platform_isOSX;
                    if v___x_5538_ == 0 {
                        v___x_5539_ = l_System_Platform_isWindows;
                        if v___x_5539_ == 0 {
                            v_toContext_5540_ = lean_ctor_get(v___y_5497_, 1);
                            v_lakeEnv_5541_ = lean_ctor_get(v_toContext_5540_, 0);
                            v_lean_5542_ = lean_ctor_get(v_lakeEnv_5541_, 1);
                            v_log_5543_ = lean_ctor_get(v___y_5498_, 0);
                            v_action_5544_ = lean_ctor_get_uint8(
                                v___y_5498_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            v_wantsRebuild_5545_ = lean_ctor_get_uint8(
                                v___y_5498_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            );
                            v_trace_5546_ = lean_ctor_get(v___y_5498_, 1);
                            v_buildTime_5547_ = lean_ctor_get(v___y_5498_, 2);
                            v_isSharedCheck_5577_ = (!lean_is_exclusive(v___y_5498_)) as u8;
                            if v_isSharedCheck_5577_ == 0 {
                                v___x_5549_ = v___y_5498_;
                                v_isShared_5550_ = v_isSharedCheck_5577_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_buildTime_5547_);
                                lean_inc(v_trace_5546_);
                                lean_inc(v_log_5543_);
                                lean_dec(v___y_5498_);
                                v___x_5549_ = lean_box(0);
                                v_isShared_5550_ = v_isSharedCheck_5577_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_toContext_5578_ = lean_ctor_get(v___y_5497_, 1);
                            v_lakeEnv_5579_ = lean_ctor_get(v_toContext_5578_, 0);
                            v_lean_5580_ = lean_ctor_get(v_lakeEnv_5579_, 1);
                            v_log_5581_ = lean_ctor_get(v___y_5498_, 0);
                            v_action_5582_ = lean_ctor_get_uint8(
                                v___y_5498_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            v_wantsRebuild_5583_ = lean_ctor_get_uint8(
                                v___y_5498_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            );
                            v_trace_5584_ = lean_ctor_get(v___y_5498_, 1);
                            v_buildTime_5585_ = lean_ctor_get(v___y_5498_, 2);
                            v_isSharedCheck_5615_ = (!lean_is_exclusive(v___y_5498_)) as u8;
                            if v_isSharedCheck_5615_ == 0 {
                                v___x_5587_ = v___y_5498_;
                                v_isShared_5588_ = v_isSharedCheck_5615_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_buildTime_5585_);
                                lean_inc(v_trace_5584_);
                                lean_inc(v_log_5581_);
                                lean_dec(v___y_5498_);
                                v___x_5587_ = lean_box(0);
                                v_isShared_5588_ = v_isSharedCheck_5615_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        v_log_5616_ = lean_ctor_get(v___y_5498_, 0);
                        v_action_5617_ = lean_ctor_get_uint8(
                            v___y_5498_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_wantsRebuild_5618_ = lean_ctor_get_uint8(
                            v___y_5498_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_trace_5619_ = lean_ctor_get(v___y_5498_, 1);
                        v_buildTime_5620_ = lean_ctor_get(v___y_5498_, 2);
                        lean_inc_ref(v___y_5488_);
                        v___x_5621_ = l_Lake_createParentDirs(v___y_5488_);
                        if lean_obj_tag(v___x_5621_) == 0 {
                            lean_dec_ref_known(v___x_5621_, 1);
                            v___x_5622_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0;
                            lean_inc_ref(v___y_5488_);
                            v___x_5623_ = l_System_FilePath_addExtension(v___y_5488_, v___x_5622_);
                            v___x_5676_ = 1;
                            v___x_5677_ = lean_io_prim_handle_mk(v___x_5623_, v___x_5676_);
                            if lean_obj_tag(v___x_5677_) == 0 {
                                v_a_5678_ = lean_ctor_get(v___x_5677_, 0);
                                lean_inc(v_a_5678_);
                                lean_dec_ref_known(v___x_5677_, 1);
                                v___x_5679_ = lean_unsigned_to_nat(0);
                                v___x_5680_ = lean_array_get_size(v_oFiles_5489_);
                                v___x_5681_ = lean_nat_dec_lt(v___x_5679_, v___x_5680_);
                                if v___x_5681_ == 0 {
                                    lean_dec(v_a_5678_);
                                    lean_dec_ref(v_oFiles_5489_);
                                    v_a_5625_ = v___y_5498_;
                                    state = 22;
                                    continue;
                                } else {
                                    v___x_5682_ = lean_box(0);
                                    v___x_5683_ = lean_nat_dec_le(v___x_5680_, v___x_5680_);
                                    if v___x_5683_ == 0 {
                                        if v___x_5681_ == 0 {
                                            lean_dec(v_a_5678_);
                                            lean_dec_ref(v_oFiles_5489_);
                                            v_a_5625_ = v___y_5498_;
                                            state = 22;
                                            continue;
                                        } else {
                                            v___x_5684_ = lean_usize_of_nat(v___x_5680_);
                                            v___x_5685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_5678_, v_oFiles_5489_, v___x_5492_, v___x_5684_, v___x_5682_, v___y_5498_);
                                            lean_dec_ref(v_oFiles_5489_);
                                            lean_dec(v_a_5678_);
                                            v___y_5674_ = v___x_5685_;
                                            state = 30;
                                            continue;
                                        }
                                    } else {
                                        v___x_5686_ = lean_usize_of_nat(v___x_5680_);
                                        v___x_5687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_5678_, v_oFiles_5489_, v___x_5492_, v___x_5686_, v___x_5682_, v___y_5498_);
                                        lean_dec_ref(v_oFiles_5489_);
                                        lean_dec(v_a_5678_);
                                        v___y_5674_ = v___x_5687_;
                                        state = 30;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc(v_buildTime_5620_);
                                lean_inc_ref(v_trace_5619_);
                                lean_inc_ref(v_log_5616_);
                                lean_dec_ref(v___x_5623_);
                                lean_dec_ref(v_oFiles_5489_);
                                lean_dec_ref(v___y_5488_);
                                v_isSharedCheck_5701_ = (!lean_is_exclusive(v___y_5498_)) as u8;
                                if v_isSharedCheck_5701_ == 0 {
                                    v_unused_5702_ = lean_ctor_get(v___y_5498_, 2);
                                    lean_dec(v_unused_5702_);
                                    v_unused_5703_ = lean_ctor_get(v___y_5498_, 1);
                                    lean_dec(v_unused_5703_);
                                    v_unused_5704_ = lean_ctor_get(v___y_5498_, 0);
                                    lean_dec(v_unused_5704_);
                                    v___x_5689_ = v___y_5498_;
                                    v_isShared_5690_ = v_isSharedCheck_5701_;
                                    state = 31;
                                    continue;
                                } else {
                                    lean_dec(v___y_5498_);
                                    v___x_5689_ = lean_box(0);
                                    v_isShared_5690_ = v_isSharedCheck_5701_;
                                    state = 31;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v_buildTime_5620_);
                            lean_inc_ref(v_trace_5619_);
                            lean_inc_ref(v_log_5616_);
                            lean_dec_ref(v_oFiles_5489_);
                            lean_dec_ref(v___y_5488_);
                            v_isSharedCheck_5718_ = (!lean_is_exclusive(v___y_5498_)) as u8;
                            if v_isSharedCheck_5718_ == 0 {
                                v_unused_5719_ = lean_ctor_get(v___y_5498_, 2);
                                lean_dec(v_unused_5719_);
                                v_unused_5720_ = lean_ctor_get(v___y_5498_, 1);
                                lean_dec(v_unused_5720_);
                                v_unused_5721_ = lean_ctor_get(v___y_5498_, 0);
                                lean_dec(v_unused_5721_);
                                v___x_5706_ = v___y_5498_;
                                v_isShared_5707_ = v_isSharedCheck_5718_;
                                state = 33;
                                continue;
                            } else {
                                lean_dec(v___y_5498_);
                                v___x_5706_ = lean_box(0);
                                v_isShared_5707_ = v_isSharedCheck_5718_;
                                state = 33;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_ar_5511_ = lean_ctor_get(v_lean_5502_, 13);
                lean_inc_ref(v_ar_5511_);
                v___x_5512_ = l_Lake_compileStaticLib(
                    v___y_5488_,
                    v_oFiles_5489_,
                    v_ar_5511_,
                    v_bootstrap_5487_,
                    v_log_5503_,
                );
                if lean_obj_tag(v___x_5512_) == 0 {
                    v_a_5513_ = lean_ctor_get(v___x_5512_, 0);
                    v_a_5514_ = lean_ctor_get(v___x_5512_, 1);
                    v_isSharedCheck_5524_ = (!lean_is_exclusive(v___x_5512_)) as u8;
                    if v_isSharedCheck_5524_ == 0 {
                        v___x_5516_ = v___x_5512_;
                        v_isShared_5517_ = v_isSharedCheck_5524_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5514_);
                        lean_inc(v_a_5513_);
                        lean_dec(v___x_5512_);
                        v___x_5516_ = lean_box(0);
                        v_isShared_5517_ = v_isSharedCheck_5524_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5525_ = lean_ctor_get(v___x_5512_, 0);
                    v_a_5526_ = lean_ctor_get(v___x_5512_, 1);
                    v_isSharedCheck_5536_ = (!lean_is_exclusive(v___x_5512_)) as u8;
                    if v_isSharedCheck_5536_ == 0 {
                        v___x_5528_ = v___x_5512_;
                        v_isShared_5529_ = v_isSharedCheck_5536_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5526_);
                        lean_inc(v_a_5525_);
                        lean_dec(v___x_5512_);
                        v___x_5528_ = lean_box(0);
                        v_isShared_5529_ = v_isSharedCheck_5536_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5510_ == 0 {
                    lean_ctor_set(v___x_5509_, 0, v_a_5514_);
                    v___x_5519_ = v___x_5509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_a_5514_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_trace_5506_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_buildTime_5507_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5523_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5504_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5523_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5505_,
                    );
                    v___x_5519_ = v_reuseFailAlloc_5523_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5517_ == 0 {
                    lean_ctor_set(v___x_5516_, 1, v___x_5519_);
                    v___x_5521_ = v___x_5516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5513_);
                    lean_ctor_set(v_reuseFailAlloc_5522_, 1, v___x_5519_);
                    v___x_5521_ = v_reuseFailAlloc_5522_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5521_;
            }
            5 => {
                if v_isShared_5510_ == 0 {
                    lean_ctor_set(v___x_5509_, 0, v_a_5526_);
                    v___x_5531_ = v___x_5509_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5526_);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 1, v_trace_5506_);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 2, v_buildTime_5507_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5535_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5504_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5535_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5505_,
                    );
                    v___x_5531_ = v_reuseFailAlloc_5535_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5529_ == 0 {
                    lean_ctor_set(v___x_5528_, 1, v___x_5531_);
                    v___x_5533_ = v___x_5528_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5534_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_a_5525_);
                    lean_ctor_set(v_reuseFailAlloc_5534_, 1, v___x_5531_);
                    v___x_5533_ = v_reuseFailAlloc_5534_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5533_;
            }
            8 => {
                v_ar_5551_ = lean_ctor_get(v_lean_5542_, 13);
                lean_inc_ref(v_ar_5551_);
                v___x_5552_ = l_Lake_compileStaticLib(
                    v___y_5488_,
                    v_oFiles_5489_,
                    v_ar_5551_,
                    v___x_5539_,
                    v_log_5543_,
                );
                if lean_obj_tag(v___x_5552_) == 0 {
                    v_a_5553_ = lean_ctor_get(v___x_5552_, 0);
                    v_a_5554_ = lean_ctor_get(v___x_5552_, 1);
                    v_isSharedCheck_5564_ = (!lean_is_exclusive(v___x_5552_)) as u8;
                    if v_isSharedCheck_5564_ == 0 {
                        v___x_5556_ = v___x_5552_;
                        v_isShared_5557_ = v_isSharedCheck_5564_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5554_);
                        lean_inc(v_a_5553_);
                        lean_dec(v___x_5552_);
                        v___x_5556_ = lean_box(0);
                        v_isShared_5557_ = v_isSharedCheck_5564_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_5565_ = lean_ctor_get(v___x_5552_, 0);
                    v_a_5566_ = lean_ctor_get(v___x_5552_, 1);
                    v_isSharedCheck_5576_ = (!lean_is_exclusive(v___x_5552_)) as u8;
                    if v_isSharedCheck_5576_ == 0 {
                        v___x_5568_ = v___x_5552_;
                        v_isShared_5569_ = v_isSharedCheck_5576_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_5566_);
                        lean_inc(v_a_5565_);
                        lean_dec(v___x_5552_);
                        v___x_5568_ = lean_box(0);
                        v_isShared_5569_ = v_isSharedCheck_5576_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_5550_ == 0 {
                    lean_ctor_set(v___x_5549_, 0, v_a_5554_);
                    v___x_5559_ = v___x_5549_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5554_);
                    lean_ctor_set(v_reuseFailAlloc_5563_, 1, v_trace_5546_);
                    lean_ctor_set(v_reuseFailAlloc_5563_, 2, v_buildTime_5547_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5563_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5544_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5563_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5545_,
                    );
                    v___x_5559_ = v_reuseFailAlloc_5563_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5557_ == 0 {
                    lean_ctor_set(v___x_5556_, 1, v___x_5559_);
                    v___x_5561_ = v___x_5556_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5562_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5553_);
                    lean_ctor_set(v_reuseFailAlloc_5562_, 1, v___x_5559_);
                    v___x_5561_ = v_reuseFailAlloc_5562_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5561_;
            }
            12 => {
                if v_isShared_5550_ == 0 {
                    lean_ctor_set(v___x_5549_, 0, v_a_5566_);
                    v___x_5571_ = v___x_5549_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_a_5566_);
                    lean_ctor_set(v_reuseFailAlloc_5575_, 1, v_trace_5546_);
                    lean_ctor_set(v_reuseFailAlloc_5575_, 2, v_buildTime_5547_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5575_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5544_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5575_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5545_,
                    );
                    v___x_5571_ = v_reuseFailAlloc_5575_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5569_ == 0 {
                    lean_ctor_set(v___x_5568_, 1, v___x_5571_);
                    v___x_5573_ = v___x_5568_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5574_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5565_);
                    lean_ctor_set(v_reuseFailAlloc_5574_, 1, v___x_5571_);
                    v___x_5573_ = v_reuseFailAlloc_5574_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5573_;
            }
            15 => {
                v_ar_5589_ = lean_ctor_get(v_lean_5580_, 13);
                lean_inc_ref(v_ar_5589_);
                v___x_5590_ = l_Lake_compileStaticLib(
                    v___y_5488_,
                    v_oFiles_5489_,
                    v_ar_5589_,
                    v_shouldExport_5490_,
                    v_log_5581_,
                );
                if lean_obj_tag(v___x_5590_) == 0 {
                    v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
                    v_a_5592_ = lean_ctor_get(v___x_5590_, 1);
                    v_isSharedCheck_5602_ = (!lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5602_ == 0 {
                        v___x_5594_ = v___x_5590_;
                        v_isShared_5595_ = v_isSharedCheck_5602_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_5592_);
                        lean_inc(v_a_5591_);
                        lean_dec(v___x_5590_);
                        v___x_5594_ = lean_box(0);
                        v_isShared_5595_ = v_isSharedCheck_5602_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_a_5603_ = lean_ctor_get(v___x_5590_, 0);
                    v_a_5604_ = lean_ctor_get(v___x_5590_, 1);
                    v_isSharedCheck_5614_ = (!lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5614_ == 0 {
                        v___x_5606_ = v___x_5590_;
                        v_isShared_5607_ = v_isSharedCheck_5614_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_5604_);
                        lean_inc(v_a_5603_);
                        lean_dec(v___x_5590_);
                        v___x_5606_ = lean_box(0);
                        v_isShared_5607_ = v_isSharedCheck_5614_;
                        state = 19;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_5588_ == 0 {
                    lean_ctor_set(v___x_5587_, 0, v_a_5592_);
                    v___x_5597_ = v___x_5587_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5592_);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 1, v_trace_5584_);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 2, v_buildTime_5585_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5601_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5582_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5601_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5583_,
                    );
                    v___x_5597_ = v_reuseFailAlloc_5601_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_5595_ == 0 {
                    lean_ctor_set(v___x_5594_, 1, v___x_5597_);
                    v___x_5599_ = v___x_5594_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5600_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_a_5591_);
                    lean_ctor_set(v_reuseFailAlloc_5600_, 1, v___x_5597_);
                    v___x_5599_ = v_reuseFailAlloc_5600_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5599_;
            }
            19 => {
                if v_isShared_5588_ == 0 {
                    lean_ctor_set(v___x_5587_, 0, v_a_5604_);
                    v___x_5609_ = v___x_5587_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5604_);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 1, v_trace_5584_);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 2, v_buildTime_5585_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5613_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5582_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5613_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5583_,
                    );
                    v___x_5609_ = v_reuseFailAlloc_5613_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_5607_ == 0 {
                    lean_ctor_set(v___x_5606_, 1, v___x_5609_);
                    v___x_5611_ = v___x_5606_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5603_);
                    lean_ctor_set(v_reuseFailAlloc_5612_, 1, v___x_5609_);
                    v___x_5611_ = v_reuseFailAlloc_5612_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5611_;
            }
            22 => {
                v___x_5626_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1;
                v_log_5627_ = lean_ctor_get(v_a_5625_, 0);
                v_action_5628_ = lean_ctor_get_uint8(
                    v_a_5625_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5629_ = lean_ctor_get_uint8(
                    v_a_5625_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_5630_ = lean_ctor_get(v_a_5625_, 1);
                v_buildTime_5631_ = lean_ctor_get(v_a_5625_, 2);
                v_isSharedCheck_5672_ = (!lean_is_exclusive(v_a_5625_)) as u8;
                if v_isSharedCheck_5672_ == 0 {
                    v___x_5633_ = v_a_5625_;
                    v_isShared_5634_ = v_isSharedCheck_5672_;
                    state = 23;
                    continue;
                } else {
                    lean_inc(v_buildTime_5631_);
                    lean_inc(v_trace_5630_);
                    lean_inc(v_log_5627_);
                    lean_dec(v_a_5625_);
                    v___x_5633_ = lean_box(0);
                    v_isShared_5634_ = v_isSharedCheck_5672_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_5635_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2;
                v___x_5636_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5;
                v___x_5637_ = lean_unsigned_to_nat(5);
                v___x_5638_ = lean_mk_empty_array_with_capacity(v___x_5637_);
                lean_dec_ref(v___x_5638_);
                v___x_5639_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once), _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
                v___x_5640_ = lean_array_push(v___x_5639_, v___y_5488_);
                v___x_5641_ = lean_array_push(v___x_5640_, v___x_5636_);
                v___x_5642_ = lean_array_push(v___x_5641_, v___x_5623_);
                v___x_5643_ = lean_box(0);
                v___x_5644_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8;
                v___x_5645_ = 0;
                v___x_5646_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_5646_, 0, v___x_5626_);
                lean_ctor_set(v___x_5646_, 1, v___x_5635_);
                lean_ctor_set(v___x_5646_, 2, v___x_5642_);
                lean_ctor_set(v___x_5646_, 3, v___x_5643_);
                lean_ctor_set(v___x_5646_, 4, v___x_5644_);
                lean_ctor_set_uint8(
                    v___x_5646_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_5491_,
                );
                lean_ctor_set_uint8(
                    v___x_5646_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_5645_,
                );
                v___x_5647_ = l_Lake_proc(v___x_5646_, v___x_5645_, v_log_5627_);
                if lean_obj_tag(v___x_5647_) == 0 {
                    v_a_5648_ = lean_ctor_get(v___x_5647_, 0);
                    v_a_5649_ = lean_ctor_get(v___x_5647_, 1);
                    v_isSharedCheck_5659_ = (!lean_is_exclusive(v___x_5647_)) as u8;
                    if v_isSharedCheck_5659_ == 0 {
                        v___x_5651_ = v___x_5647_;
                        v_isShared_5652_ = v_isSharedCheck_5659_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_5649_);
                        lean_inc(v_a_5648_);
                        lean_dec(v___x_5647_);
                        v___x_5651_ = lean_box(0);
                        v_isShared_5652_ = v_isSharedCheck_5659_;
                        state = 24;
                        continue;
                    }
                } else {
                    v_a_5660_ = lean_ctor_get(v___x_5647_, 0);
                    v_a_5661_ = lean_ctor_get(v___x_5647_, 1);
                    v_isSharedCheck_5671_ = (!lean_is_exclusive(v___x_5647_)) as u8;
                    if v_isSharedCheck_5671_ == 0 {
                        v___x_5663_ = v___x_5647_;
                        v_isShared_5664_ = v_isSharedCheck_5671_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_5661_);
                        lean_inc(v_a_5660_);
                        lean_dec(v___x_5647_);
                        v___x_5663_ = lean_box(0);
                        v_isShared_5664_ = v_isSharedCheck_5671_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_5634_ == 0 {
                    lean_ctor_set(v___x_5633_, 0, v_a_5649_);
                    v___x_5654_ = v___x_5633_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_a_5649_);
                    lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_trace_5630_);
                    lean_ctor_set(v_reuseFailAlloc_5658_, 2, v_buildTime_5631_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5658_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5628_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5658_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5629_,
                    );
                    v___x_5654_ = v_reuseFailAlloc_5658_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_5652_ == 0 {
                    lean_ctor_set(v___x_5651_, 1, v___x_5654_);
                    v___x_5656_ = v___x_5651_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5648_);
                    lean_ctor_set(v_reuseFailAlloc_5657_, 1, v___x_5654_);
                    v___x_5656_ = v_reuseFailAlloc_5657_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5656_;
            }
            27 => {
                if v_isShared_5634_ == 0 {
                    lean_ctor_set(v___x_5633_, 0, v_a_5661_);
                    v___x_5666_ = v___x_5633_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5670_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5661_);
                    lean_ctor_set(v_reuseFailAlloc_5670_, 1, v_trace_5630_);
                    lean_ctor_set(v_reuseFailAlloc_5670_, 2, v_buildTime_5631_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5670_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5628_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5670_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5629_,
                    );
                    v___x_5666_ = v_reuseFailAlloc_5670_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_5664_ == 0 {
                    lean_ctor_set(v___x_5663_, 1, v___x_5666_);
                    v___x_5668_ = v___x_5663_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5669_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5660_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 1, v___x_5666_);
                    v___x_5668_ = v_reuseFailAlloc_5669_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5668_;
            }
            30 => {
                if lean_obj_tag(v___y_5674_) == 0 {
                    v_a_5675_ = lean_ctor_get(v___y_5674_, 1);
                    lean_inc(v_a_5675_);
                    lean_dec_ref_known(v___y_5674_, 2);
                    v_a_5625_ = v_a_5675_;
                    state = 22;
                    continue;
                } else {
                    lean_dec_ref(v___x_5623_);
                    lean_dec_ref(v___y_5488_);
                    return v___y_5674_;
                }
            }
            31 => {
                v_a_5691_ = lean_ctor_get(v___x_5677_, 0);
                lean_inc(v_a_5691_);
                lean_dec_ref_known(v___x_5677_, 1);
                v___x_5692_ = lean_io_error_to_string(v_a_5691_);
                v___x_5693_ = 3;
                v___x_5694_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5694_, 0, v___x_5692_);
                lean_ctor_set_uint8(
                    v___x_5694_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5693_,
                );
                v___x_5695_ = lean_array_get_size(v_log_5616_);
                v___x_5696_ = lean_array_push(v_log_5616_, v___x_5694_);
                if v_isShared_5690_ == 0 {
                    lean_ctor_set(v___x_5689_, 0, v___x_5696_);
                    v___x_5698_ = v___x_5689_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5696_);
                    lean_ctor_set(v_reuseFailAlloc_5700_, 1, v_trace_5619_);
                    lean_ctor_set(v_reuseFailAlloc_5700_, 2, v_buildTime_5620_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5700_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5617_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5700_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5618_,
                    );
                    v___x_5698_ = v_reuseFailAlloc_5700_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_5699_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5699_, 0, v___x_5695_);
                lean_ctor_set(v___x_5699_, 1, v___x_5698_);
                return v___x_5699_;
            }
            33 => {
                v_a_5708_ = lean_ctor_get(v___x_5621_, 0);
                lean_inc(v_a_5708_);
                lean_dec_ref_known(v___x_5621_, 1);
                v___x_5709_ = lean_io_error_to_string(v_a_5708_);
                v___x_5710_ = 3;
                v___x_5711_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5711_, 0, v___x_5709_);
                lean_ctor_set_uint8(
                    v___x_5711_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5710_,
                );
                v___x_5712_ = lean_array_get_size(v_log_5616_);
                v___x_5713_ = lean_array_push(v_log_5616_, v___x_5711_);
                if v_isShared_5707_ == 0 {
                    lean_ctor_set(v___x_5706_, 0, v___x_5713_);
                    v___x_5715_ = v___x_5706_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5717_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5717_, 0, v___x_5713_);
                    lean_ctor_set(v_reuseFailAlloc_5717_, 1, v_trace_5619_);
                    lean_ctor_set(v_reuseFailAlloc_5717_, 2, v_buildTime_5620_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5717_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5617_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5717_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5618_,
                    );
                    v___x_5715_ = v_reuseFailAlloc_5717_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v___x_5716_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5716_, 0, v___x_5712_);
                lean_ctor_set(v___x_5716_, 1, v___x_5715_);
                return v___x_5716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(
    mut v_bootstrap_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v_oFiles_5724_: *mut LeanObject,
    mut v_shouldExport_5725_: *mut LeanObject,
    mut v___x_5726_: *mut LeanObject,
    mut v___x_5727_: *mut LeanObject,
    mut v___y_5728_: *mut LeanObject,
    mut v___y_5729_: *mut LeanObject,
    mut v___y_5730_: *mut LeanObject,
    mut v___y_5731_: *mut LeanObject,
    mut v___y_5732_: *mut LeanObject,
    mut v___y_5733_: *mut LeanObject,
    mut v___y_5734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bootstrap_boxed_5735_: u8 = 0;
    let mut v_shouldExport_boxed_5736_: u8 = 0;
    let mut v___x_6740__boxed_5737_: u8 = 0;
    let mut v___x_6741__boxed_5738_: usize = 0;
    let mut v_res_5739_: *mut LeanObject = core::ptr::null_mut();
    v_bootstrap_boxed_5735_ = (lean_unbox(v_bootstrap_5722_) as u8);
    v_shouldExport_boxed_5736_ = (lean_unbox(v_shouldExport_5725_) as u8);
    v___x_6740__boxed_5737_ = (lean_unbox(v___x_5726_) as u8);
    v___x_6741__boxed_5738_ = lean_unbox_usize(v___x_5727_);
    lean_dec(v___x_5727_);
    v_res_5739_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_5735_, v___y_5723_, v_oFiles_5724_, v_shouldExport_boxed_5736_, v___x_6740__boxed_5737_, v___x_6741__boxed_5738_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
    lean_dec_ref(v___y_5732_);
    lean_dec(v___y_5731_);
    lean_dec(v___y_5730_);
    lean_dec(v___y_5729_);
    lean_dec_ref(v___y_5728_);
    return v_res_5739_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(
    mut v_bootstrap_5740_: u8,
    mut v___y_5741_: *mut LeanObject,
    mut v_shouldExport_5742_: u8,
    mut v___x_5743_: u8,
    mut v___x_5744_: usize,
    mut v_oFiles_5745_: *mut LeanObject,
    mut v___y_5746_: *mut LeanObject,
    mut v___y_5747_: *mut LeanObject,
    mut v___y_5748_: *mut LeanObject,
    mut v___y_5749_: *mut LeanObject,
    mut v___y_5750_: *mut LeanObject,
    mut v___y_5751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: u8 = 0;
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5765_: u8 = 0;
    let mut v_path_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5770_: u8 = 0;
    let mut v_a_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5753_ = lean_box((v_bootstrap_5740_) as usize);
                v___x_5754_ = lean_box((v_shouldExport_5742_) as usize);
                v___x_5755_ = lean_box((v___x_5743_) as usize);
                v___x_5756_ = lean_box_usize(v___x_5744_);
                lean_inc_ref(v___y_5741_);
                v___y_5757_ = lean_alloc_closure(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed as *mut core::ffi::c_void, 13, 6);
                lean_closure_set(v___y_5757_, 0, v___x_5753_);
                lean_closure_set(v___y_5757_, 1, v___y_5741_);
                lean_closure_set(v___y_5757_, 2, v_oFiles_5745_);
                lean_closure_set(v___y_5757_, 3, v___x_5754_);
                lean_closure_set(v___y_5757_, 4, v___x_5755_);
                lean_closure_set(v___y_5757_, 5, v___x_5756_);
                v___x_5758_ = 0;
                v___x_5759_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0;
                v___x_5760_ = l_Lake_buildArtifactUnlessUpToDate(
                    v___y_5741_,
                    v___y_5757_,
                    v___x_5758_,
                    v___x_5759_,
                    v___x_5743_,
                    v___x_5758_,
                    v___x_5758_,
                    v___y_5746_,
                    v___y_5747_,
                    v___y_5748_,
                    v___y_5749_,
                    v___y_5750_,
                    v___y_5751_,
                );
                if lean_obj_tag(v___x_5760_) == 0 {
                    v_a_5761_ = lean_ctor_get(v___x_5760_, 0);
                    v_a_5762_ = lean_ctor_get(v___x_5760_, 1);
                    v_isSharedCheck_5770_ = (!lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5770_ == 0 {
                        v___x_5764_ = v___x_5760_;
                        v_isShared_5765_ = v_isSharedCheck_5770_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5762_);
                        lean_inc(v_a_5761_);
                        lean_dec(v___x_5760_);
                        v___x_5764_ = lean_box(0);
                        v_isShared_5765_ = v_isSharedCheck_5770_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5771_ = lean_ctor_get(v___x_5760_, 0);
                    v_a_5772_ = lean_ctor_get(v___x_5760_, 1);
                    v_isSharedCheck_5779_ = (!lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5779_ == 0 {
                        v___x_5774_ = v___x_5760_;
                        v_isShared_5775_ = v_isSharedCheck_5779_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5772_);
                        lean_inc(v_a_5771_);
                        lean_dec(v___x_5760_);
                        v___x_5774_ = lean_box(0);
                        v_isShared_5775_ = v_isSharedCheck_5779_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_path_5766_ = lean_ctor_get(v_a_5761_, 1);
                lean_inc_ref(v_path_5766_);
                lean_dec(v_a_5761_);
                if v_isShared_5765_ == 0 {
                    lean_ctor_set(v___x_5764_, 0, v_path_5766_);
                    v___x_5768_ = v___x_5764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5769_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_path_5766_);
                    lean_ctor_set(v_reuseFailAlloc_5769_, 1, v_a_5762_);
                    v___x_5768_ = v_reuseFailAlloc_5769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5768_;
            }
            3 => {
                if v_isShared_5775_ == 0 {
                    v___x_5777_ = v___x_5774_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5778_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_a_5771_);
                    lean_ctor_set(v_reuseFailAlloc_5778_, 1, v_a_5772_);
                    v___x_5777_ = v_reuseFailAlloc_5778_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(
    mut v_bootstrap_5780_: *mut LeanObject,
    mut v___y_5781_: *mut LeanObject,
    mut v_shouldExport_5782_: *mut LeanObject,
    mut v___x_5783_: *mut LeanObject,
    mut v___x_5784_: *mut LeanObject,
    mut v_oFiles_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
    mut v___y_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bootstrap_boxed_5793_: u8 = 0;
    let mut v_shouldExport_boxed_5794_: u8 = 0;
    let mut v___x_7150__boxed_5795_: u8 = 0;
    let mut v___x_7151__boxed_5796_: usize = 0;
    let mut v_res_5797_: *mut LeanObject = core::ptr::null_mut();
    v_bootstrap_boxed_5793_ = (lean_unbox(v_bootstrap_5780_) as u8);
    v_shouldExport_boxed_5794_ = (lean_unbox(v_shouldExport_5782_) as u8);
    v___x_7150__boxed_5795_ = (lean_unbox(v___x_5783_) as u8);
    v___x_7151__boxed_5796_ = lean_unbox_usize(v___x_5784_);
    lean_dec(v___x_5784_);
    v_res_5797_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_5793_, v___y_5781_, v_shouldExport_boxed_5794_, v___x_7150__boxed_5795_, v___x_7151__boxed_5796_, v_oFiles_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_);
    lean_dec_ref(v___y_5790_);
    lean_dec(v___y_5789_);
    lean_dec(v___y_5788_);
    lean_dec(v___y_5787_);
    return v_res_5797_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(
    mut v_a_5798_: *mut LeanObject,
    mut v_sz_5799_: usize,
    mut v_i_5800_: usize,
    mut v_bs_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
    mut v___y_5805_: *mut LeanObject,
    mut v___y_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5809_: u8 = 0;
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: usize = 0;
    let mut v___x_5818_: usize = 0;
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5825_: u8 = 0;
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5809_ = lean_usize_dec_lt(v_i_5800_, v_sz_5799_);
                if v___x_5809_ == 0 {
                    lean_dec_ref(v___y_5802_);
                    lean_dec_ref(v_a_5798_);
                    v___x_5810_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5810_, 0, v_bs_5801_);
                    lean_ctor_set(v___x_5810_, 1, v___y_5807_);
                    return v___x_5810_;
                } else {
                    v_v_5811_ = lean_array_uget_borrowed(v_bs_5801_, v_i_5800_);
                    lean_inc_ref(v___y_5802_);
                    lean_inc_ref(v_a_5798_);
                    lean_inc(v_v_5811_);
                    v___x_5812_ = l_Lake_ModuleFacet_fetch___redArg(
                        v_v_5811_,
                        v_a_5798_,
                        v___y_5802_,
                        v___y_5803_,
                        v___y_5804_,
                        v___y_5805_,
                        v___y_5806_,
                        v___y_5807_,
                    );
                    if lean_obj_tag(v___x_5812_) == 0 {
                        v_a_5813_ = lean_ctor_get(v___x_5812_, 0);
                        lean_inc(v_a_5813_);
                        v_a_5814_ = lean_ctor_get(v___x_5812_, 1);
                        lean_inc(v_a_5814_);
                        lean_dec_ref_known(v___x_5812_, 2);
                        v___x_5815_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5816_ = lean_array_uset(v_bs_5801_, v_i_5800_, v___x_5815_);
                        v___x_5817_ = 1usize;
                        v___x_5818_ = lean_usize_add(v_i_5800_, v___x_5817_);
                        v___x_5819_ = lean_array_uset(v_bs_x27_5816_, v_i_5800_, v_a_5813_);
                        v_i_5800_ = v___x_5818_;
                        v_bs_5801_ = v___x_5819_;
                        v___y_5807_ = v_a_5814_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_5802_);
                        lean_dec_ref(v_bs_5801_);
                        lean_dec_ref(v_a_5798_);
                        v_a_5821_ = lean_ctor_get(v___x_5812_, 0);
                        v_a_5822_ = lean_ctor_get(v___x_5812_, 1);
                        v_isSharedCheck_5829_ = (!lean_is_exclusive(v___x_5812_)) as u8;
                        if v_isSharedCheck_5829_ == 0 {
                            v___x_5824_ = v___x_5812_;
                            v_isShared_5825_ = v_isSharedCheck_5829_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5822_);
                            lean_inc(v_a_5821_);
                            lean_dec(v___x_5812_);
                            v___x_5824_ = lean_box(0);
                            v_isShared_5825_ = v_isSharedCheck_5829_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5825_ == 0 {
                    v___x_5827_ = v___x_5824_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5828_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_a_5821_);
                    lean_ctor_set(v_reuseFailAlloc_5828_, 1, v_a_5822_);
                    v___x_5827_ = v_reuseFailAlloc_5828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(
    mut v_a_5830_: *mut LeanObject,
    mut v_sz_5831_: *mut LeanObject,
    mut v_i_5832_: *mut LeanObject,
    mut v_bs_5833_: *mut LeanObject,
    mut v___y_5834_: *mut LeanObject,
    mut v___y_5835_: *mut LeanObject,
    mut v___y_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
    mut v___y_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5841_: usize = 0;
    let mut v_i_boxed_5842_: usize = 0;
    let mut v_res_5843_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5841_ = lean_unbox_usize(v_sz_5831_);
    lean_dec(v_sz_5831_);
    v_i_boxed_5842_ = lean_unbox_usize(v_i_5832_);
    lean_dec(v_i_5832_);
    v_res_5843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_5830_, v_sz_boxed_5841_, v_i_boxed_5842_, v_bs_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
    lean_dec_ref(v___y_5838_);
    lean_dec(v___y_5837_);
    lean_dec(v___y_5836_);
    lean_dec(v___y_5835_);
    return v_res_5843_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(
    mut v_shouldExport_5844_: u8,
    mut v_as_5845_: *mut LeanObject,
    mut v_i_5846_: usize,
    mut v_stop_5847_: usize,
    mut v_b_5848_: *mut LeanObject,
    mut v___y_5849_: *mut LeanObject,
    mut v___y_5850_: *mut LeanObject,
    mut v___y_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5856_: u8 = 0;
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5863_: usize = 0;
    let mut v___x_5864_: usize = 0;
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: usize = 0;
    let mut v___x_5870_: usize = 0;
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5856_ = lean_usize_dec_eq(v_i_5846_, v_stop_5847_);
                if v___x_5856_ == 0 {
                    v___x_5857_ = lean_array_uget_borrowed(v_as_5845_, v_i_5846_);
                    v_lib_5858_ = lean_ctor_get(v___x_5857_, 0);
                    v_config_5859_ = lean_ctor_get(v_lib_5858_, 2);
                    v_nativeFacets_5860_ = lean_ctor_get(v_config_5859_, 8);
                    v___x_5861_ = lean_box((v_shouldExport_5844_) as usize);
                    lean_inc_ref(v_nativeFacets_5860_);
                    v___x_5862_ = lean_apply_1(v_nativeFacets_5860_, v___x_5861_);
                    v_sz_5863_ = lean_array_size(v___x_5862_);
                    v___x_5864_ = 0usize;
                    lean_inc_ref(v___y_5849_);
                    lean_inc(v___x_5857_);
                    v___x_5865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_5857_, v_sz_5863_, v___x_5864_, v___x_5862_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
                    if lean_obj_tag(v___x_5865_) == 0 {
                        v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
                        lean_inc(v_a_5866_);
                        v_a_5867_ = lean_ctor_get(v___x_5865_, 1);
                        lean_inc(v_a_5867_);
                        lean_dec_ref_known(v___x_5865_, 2);
                        v___x_5868_ = l_Array_append___redArg(v_b_5848_, v_a_5866_);
                        lean_dec(v_a_5866_);
                        v___x_5869_ = 1usize;
                        v___x_5870_ = lean_usize_add(v_i_5846_, v___x_5869_);
                        v_i_5846_ = v___x_5870_;
                        v_b_5848_ = v___x_5868_;
                        v___y_5854_ = v_a_5867_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_5849_);
                        lean_dec_ref(v_b_5848_);
                        return v___x_5865_;
                    }
                } else {
                    lean_dec_ref(v___y_5849_);
                    v___x_5872_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5872_, 0, v_b_5848_);
                    lean_ctor_set(v___x_5872_, 1, v___y_5854_);
                    return v___x_5872_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(
    mut v_shouldExport_5873_: *mut LeanObject,
    mut v_as_5874_: *mut LeanObject,
    mut v_i_5875_: *mut LeanObject,
    mut v_stop_5876_: *mut LeanObject,
    mut v_b_5877_: *mut LeanObject,
    mut v___y_5878_: *mut LeanObject,
    mut v___y_5879_: *mut LeanObject,
    mut v___y_5880_: *mut LeanObject,
    mut v___y_5881_: *mut LeanObject,
    mut v___y_5882_: *mut LeanObject,
    mut v___y_5883_: *mut LeanObject,
    mut v___y_5884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldExport_boxed_5885_: u8 = 0;
    let mut v_i_boxed_5886_: usize = 0;
    let mut v_stop_boxed_5887_: usize = 0;
    let mut v_res_5888_: *mut LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_5885_ = (lean_unbox(v_shouldExport_5873_) as u8);
    v_i_boxed_5886_ = lean_unbox_usize(v_i_5875_);
    lean_dec(v_i_5875_);
    v_stop_boxed_5887_ = lean_unbox_usize(v_stop_5876_);
    lean_dec(v_stop_5876_);
    v_res_5888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_5885_, v_as_5874_, v_i_boxed_5886_, v_stop_boxed_5887_, v_b_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_);
    lean_dec_ref(v___y_5882_);
    lean_dec(v___y_5881_);
    lean_dec(v___y_5880_);
    lean_dec(v___y_5879_);
    lean_dec_ref(v_as_5874_);
    return v_res_5888_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(
    mut v___x_5889_: *mut LeanObject,
    mut v___x_5890_: *mut LeanObject,
    mut v_config_5891_: *mut LeanObject,
    mut v_config_5892_: *mut LeanObject,
    mut v_pkg_5893_: *mut LeanObject,
    mut v_shouldExport_5894_: u8,
    mut v___x_5895_: u8,
    mut v___x_5896_: *mut LeanObject,
    mut v_dir_5897_: *mut LeanObject,
    mut v_self_5898_: *mut LeanObject,
    mut v___y_5899_: *mut LeanObject,
    mut v___y_5900_: *mut LeanObject,
    mut v___y_5901_: *mut LeanObject,
    mut v___y_5902_: *mut LeanObject,
    mut v___y_5903_: *mut LeanObject,
    mut v___y_5904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5908_: u8 = 0;
    let mut v___y_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5910_: usize = 0;
    let mut v___y_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: u8 = 0;
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_5931_: u8 = 0;
    let mut v_buildDir_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5937_: usize = 0;
    let mut v___x_5938_: usize = 0;
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: u8 = 0;
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5965_: u8 = 0;
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5969_: u8 = 0;
    let mut v___y_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5978_: u8 = 0;
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5982_: u8 = 0;
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: u8 = 0;
    let mut v___x_5993_: u8 = 0;
    let mut v___x_5994_: usize = 0;
    let mut v___x_5995_: usize = 0;
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: usize = 0;
    let mut v___x_5998_: usize = 0;
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6004_: u8 = 0;
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6008_: u8 = 0;
    let mut v_a_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6013_: u8 = 0;
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___y_5899_);
                lean_inc_ref(v___y_5903_);
                lean_inc(v___y_5902_);
                lean_inc(v___y_5901_);
                lean_inc(v___x_5890_);
                v___x_5983_ = lean_apply_7(
                    v___y_5899_,
                    v___x_5889_,
                    v___x_5890_,
                    v___y_5901_,
                    v___y_5902_,
                    v___y_5903_,
                    v___y_5904_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5983_) == 0 {
                    v_a_5984_ = lean_ctor_get(v___x_5983_, 0);
                    lean_inc(v_a_5984_);
                    v_a_5985_ = lean_ctor_get(v___x_5983_, 1);
                    lean_inc(v_a_5985_);
                    lean_dec_ref_known(v___x_5983_, 2);
                    v___x_5986_ = l_Lake_Job_await___redArg(v_a_5984_, v_a_5985_);
                    if lean_obj_tag(v___x_5986_) == 0 {
                        v_a_5987_ = lean_ctor_get(v___x_5986_, 0);
                        lean_inc(v_a_5987_);
                        v_a_5988_ = lean_ctor_get(v___x_5986_, 1);
                        lean_inc(v_a_5988_);
                        lean_dec_ref_known(v___x_5986_, 2);
                        v___x_5989_ = lean_unsigned_to_nat(0);
                        v___x_5990_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2;
                        v___x_5991_ = lean_array_get_size(v_a_5987_);
                        v___x_5992_ = lean_nat_dec_lt(v___x_5989_, v___x_5991_);
                        if v___x_5992_ == 0 {
                            lean_dec(v_a_5987_);
                            v_a_5927_ = v___x_5990_;
                            v_a_5928_ = v_a_5988_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5993_ = lean_nat_dec_le(v___x_5991_, v___x_5991_);
                            if v___x_5993_ == 0 {
                                if v___x_5992_ == 0 {
                                    lean_dec(v_a_5987_);
                                    v_a_5927_ = v___x_5990_;
                                    v_a_5928_ = v_a_5988_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_5994_ = 0usize;
                                    v___x_5995_ = lean_usize_of_nat(v___x_5991_);
                                    lean_inc_ref(v___y_5899_);
                                    v___x_5996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_5894_, v_a_5987_, v___x_5994_, v___x_5995_, v___x_5990_, v___y_5899_, v___x_5890_, v___y_5901_, v___y_5902_, v___y_5903_, v_a_5988_);
                                    lean_dec(v_a_5987_);
                                    v___y_5971_ = v___x_5996_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v___x_5997_ = 0usize;
                                v___x_5998_ = lean_usize_of_nat(v___x_5991_);
                                lean_inc_ref(v___y_5899_);
                                v___x_5999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_5894_, v_a_5987_, v___x_5997_, v___x_5998_, v___x_5990_, v___y_5899_, v___x_5890_, v___y_5901_, v___y_5902_, v___y_5903_, v_a_5988_);
                                lean_dec(v_a_5987_);
                                v___y_5971_ = v___x_5999_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_5899_);
                        lean_dec_ref(v_self_5898_);
                        lean_dec_ref(v_dir_5897_);
                        lean_dec(v___x_5896_);
                        lean_dec_ref(v_pkg_5893_);
                        lean_dec_ref(v_config_5891_);
                        lean_dec(v___x_5890_);
                        v_a_6000_ = lean_ctor_get(v___x_5986_, 0);
                        v_a_6001_ = lean_ctor_get(v___x_5986_, 1);
                        v_isSharedCheck_6008_ = (!lean_is_exclusive(v___x_5986_)) as u8;
                        if v_isSharedCheck_6008_ == 0 {
                            v___x_6003_ = v___x_5986_;
                            v_isShared_6004_ = v_isSharedCheck_6008_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6001_);
                            lean_inc(v_a_6000_);
                            lean_dec(v___x_5986_);
                            v___x_6003_ = lean_box(0);
                            v_isShared_6004_ = v_isSharedCheck_6008_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5899_);
                    lean_dec_ref(v_self_5898_);
                    lean_dec_ref(v_dir_5897_);
                    lean_dec(v___x_5896_);
                    lean_dec_ref(v_pkg_5893_);
                    lean_dec_ref(v_config_5891_);
                    lean_dec(v___x_5890_);
                    v_a_6009_ = lean_ctor_get(v___x_5983_, 0);
                    v_a_6010_ = lean_ctor_get(v___x_5983_, 1);
                    v_isSharedCheck_6017_ = (!lean_is_exclusive(v___x_5983_)) as u8;
                    if v_isSharedCheck_6017_ == 0 {
                        v___x_6012_ = v___x_5983_;
                        v_isShared_6013_ = v_isSharedCheck_6017_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6010_);
                        lean_inc(v_a_6009_);
                        lean_dec(v___x_5983_);
                        v___x_6012_ = lean_box(0);
                        v_isShared_6013_ = v_isSharedCheck_6017_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5913_ = lean_box((v___y_5908_) as usize);
                v___x_5914_ = lean_box((v_shouldExport_5894_) as usize);
                v___x_5915_ = lean_box((v___x_5895_) as usize);
                v___x_5916_ = lean_box_usize(v___y_5910_);
                v___f_5917_ = lean_alloc_closure(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed as *mut core::ffi::c_void, 13, 5);
                lean_closure_set(v___f_5917_, 0, v___x_5913_);
                lean_closure_set(v___f_5917_, 1, v___y_5912_);
                lean_closure_set(v___f_5917_, 2, v___x_5914_);
                lean_closure_set(v___f_5917_, 3, v___x_5915_);
                lean_closure_set(v___f_5917_, 4, v___x_5916_);
                v___x_5918_ = l_Array_append___redArg(v___y_5911_, v___y_5909_);
                lean_dec_ref(v___y_5909_);
                v___x_5919_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0;
                v___x_5920_ = l_Lake_Job_collectArray___redArg(v___x_5918_, v___x_5919_);
                lean_dec_ref(v___x_5918_);
                v___x_5921_ = lean_unsigned_to_nat(0);
                v___x_5922_ = 0;
                v___x_5923_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once), _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
                v___x_5924_ = l_Lake_Job_mapM___redArg(
                    v___x_5896_,
                    v___x_5920_,
                    v___f_5917_,
                    v___x_5921_,
                    v___x_5922_,
                    v___y_5899_,
                    v___x_5890_,
                    v___y_5901_,
                    v___y_5902_,
                    v___y_5903_,
                    v___x_5923_,
                );
                lean_dec(v___x_5890_);
                v___x_5925_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5925_, 0, v___x_5924_);
                lean_ctor_set(v___x_5925_, 1, v___y_5907_);
                return v___x_5925_;
            }
            2 => {
                v_toLeanConfig_5929_ = lean_ctor_get(v_config_5891_, 1);
                lean_inc_ref(v_toLeanConfig_5929_);
                v_toLeanConfig_5930_ = lean_ctor_get(v_config_5892_, 0);
                v_bootstrap_5931_ = lean_ctor_get_uint8(
                    v_config_5891_,
                    (core::mem::size_of::<*mut LeanObject>() * 27) as u32,
                );
                v_buildDir_5932_ = lean_ctor_get(v_config_5891_, 5);
                lean_inc_ref(v_buildDir_5932_);
                v_nativeLibDir_5933_ = lean_ctor_get(v_config_5891_, 7);
                lean_inc_ref(v_nativeLibDir_5933_);
                lean_dec_ref(v_config_5891_);
                v_moreLinkObjs_5934_ = lean_ctor_get(v_toLeanConfig_5929_, 6);
                lean_inc_ref(v_moreLinkObjs_5934_);
                lean_dec_ref(v_toLeanConfig_5929_);
                v_moreLinkObjs_5935_ = lean_ctor_get(v_toLeanConfig_5930_, 6);
                v___x_5936_ = l_Array_append___redArg(v_moreLinkObjs_5934_, v_moreLinkObjs_5935_);
                v_sz_5937_ = lean_array_size(v___x_5936_);
                v___x_5938_ = 0usize;
                lean_inc_ref(v___y_5899_);
                v___x_5939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_5893_, v_sz_5937_, v___x_5938_, v___x_5936_, v___y_5899_, v___x_5890_, v___y_5901_, v___y_5902_, v___y_5903_, v_a_5928_);
                if lean_obj_tag(v___x_5939_) == 0 {
                    if v_shouldExport_5894_ == 0 {
                        v_a_5940_ = lean_ctor_get(v___x_5939_, 0);
                        lean_inc(v_a_5940_);
                        v_a_5941_ = lean_ctor_get(v___x_5939_, 1);
                        lean_inc(v_a_5941_);
                        lean_dec_ref_known(v___x_5939_, 2);
                        v___x_5942_ = l_System_FilePath_normalize(v_buildDir_5932_);
                        v___x_5943_ = l_Lake_joinRelative(v_dir_5897_, v___x_5942_);
                        v___x_5944_ = l_System_FilePath_normalize(v_nativeLibDir_5933_);
                        v___x_5945_ = l_Lake_joinRelative(v___x_5943_, v___x_5944_);
                        v___x_5946_ = l_Lake_LeanLib_libName(v_self_5898_);
                        v___x_5947_ = l_Lake_nameToStaticLib(v___x_5946_, v_shouldExport_5894_);
                        v___x_5948_ = l_Lake_joinRelative(v___x_5945_, v___x_5947_);
                        v___y_5907_ = v_a_5941_;
                        v___y_5908_ = v_bootstrap_5931_;
                        v___y_5909_ = v_a_5940_;
                        v___y_5910_ = v___x_5938_;
                        v___y_5911_ = v_a_5927_;
                        v___y_5912_ = v___x_5948_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5949_ = lean_ctor_get(v___x_5939_, 0);
                        lean_inc(v_a_5949_);
                        v_a_5950_ = lean_ctor_get(v___x_5939_, 1);
                        lean_inc(v_a_5950_);
                        lean_dec_ref_known(v___x_5939_, 2);
                        v___x_5951_ = l_System_FilePath_normalize(v_buildDir_5932_);
                        v___x_5952_ = l_Lake_joinRelative(v_dir_5897_, v___x_5951_);
                        v___x_5953_ = l_System_FilePath_normalize(v_nativeLibDir_5933_);
                        v___x_5954_ = l_Lake_joinRelative(v___x_5952_, v___x_5953_);
                        v___x_5955_ = l_Lake_LeanLib_libName(v_self_5898_);
                        v___x_5956_ = 0;
                        v___x_5957_ = l_Lake_nameToStaticLib(v___x_5955_, v___x_5956_);
                        v___x_5958_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1;
                        v___x_5959_ = l_System_FilePath_addExtension(v___x_5957_, v___x_5958_);
                        v___x_5960_ = l_Lake_joinRelative(v___x_5954_, v___x_5959_);
                        v___y_5907_ = v_a_5950_;
                        v___y_5908_ = v_bootstrap_5931_;
                        v___y_5909_ = v_a_5949_;
                        v___y_5910_ = v___x_5938_;
                        v___y_5911_ = v_a_5927_;
                        v___y_5912_ = v___x_5960_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_nativeLibDir_5933_);
                    lean_dec_ref(v_buildDir_5932_);
                    lean_dec_ref(v_a_5927_);
                    lean_dec_ref(v___y_5899_);
                    lean_dec_ref(v_self_5898_);
                    lean_dec_ref(v_dir_5897_);
                    lean_dec(v___x_5896_);
                    lean_dec(v___x_5890_);
                    v_a_5961_ = lean_ctor_get(v___x_5939_, 0);
                    v_a_5962_ = lean_ctor_get(v___x_5939_, 1);
                    v_isSharedCheck_5969_ = (!lean_is_exclusive(v___x_5939_)) as u8;
                    if v_isSharedCheck_5969_ == 0 {
                        v___x_5964_ = v___x_5939_;
                        v_isShared_5965_ = v_isSharedCheck_5969_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5962_);
                        lean_inc(v_a_5961_);
                        lean_dec(v___x_5939_);
                        v___x_5964_ = lean_box(0);
                        v_isShared_5965_ = v_isSharedCheck_5969_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5965_ == 0 {
                    v___x_5967_ = v___x_5964_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5968_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5968_, 0, v_a_5961_);
                    lean_ctor_set(v_reuseFailAlloc_5968_, 1, v_a_5962_);
                    v___x_5967_ = v_reuseFailAlloc_5968_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5967_;
            }
            5 => {
                if lean_obj_tag(v___y_5971_) == 0 {
                    v_a_5972_ = lean_ctor_get(v___y_5971_, 0);
                    lean_inc(v_a_5972_);
                    v_a_5973_ = lean_ctor_get(v___y_5971_, 1);
                    lean_inc(v_a_5973_);
                    lean_dec_ref_known(v___y_5971_, 2);
                    v_a_5927_ = v_a_5972_;
                    v_a_5928_ = v_a_5973_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v___y_5899_);
                    lean_dec_ref(v_self_5898_);
                    lean_dec_ref(v_dir_5897_);
                    lean_dec(v___x_5896_);
                    lean_dec_ref(v_pkg_5893_);
                    lean_dec_ref(v_config_5891_);
                    lean_dec(v___x_5890_);
                    v_a_5974_ = lean_ctor_get(v___y_5971_, 0);
                    v_a_5975_ = lean_ctor_get(v___y_5971_, 1);
                    v_isSharedCheck_5982_ = (!lean_is_exclusive(v___y_5971_)) as u8;
                    if v_isSharedCheck_5982_ == 0 {
                        v___x_5977_ = v___y_5971_;
                        v_isShared_5978_ = v_isSharedCheck_5982_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5975_);
                        lean_inc(v_a_5974_);
                        lean_dec(v___y_5971_);
                        v___x_5977_ = lean_box(0);
                        v_isShared_5978_ = v_isSharedCheck_5982_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5978_ == 0 {
                    v___x_5980_ = v___x_5977_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5981_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5981_, 0, v_a_5974_);
                    lean_ctor_set(v_reuseFailAlloc_5981_, 1, v_a_5975_);
                    v___x_5980_ = v_reuseFailAlloc_5981_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5980_;
            }
            8 => {
                if v_isShared_6004_ == 0 {
                    v___x_6006_ = v___x_6003_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6007_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6007_, 0, v_a_6000_);
                    lean_ctor_set(v_reuseFailAlloc_6007_, 1, v_a_6001_);
                    v___x_6006_ = v_reuseFailAlloc_6007_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6006_;
            }
            10 => {
                if v_isShared_6013_ == 0 {
                    v___x_6015_ = v___x_6012_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6016_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6009_);
                    lean_ctor_set(v_reuseFailAlloc_6016_, 1, v_a_6010_);
                    v___x_6015_ = v_reuseFailAlloc_6016_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6018_: *mut LeanObject = *_args.add(0);
    let mut v___x_6019_: *mut LeanObject = *_args.add(1);
    let mut v_config_6020_: *mut LeanObject = *_args.add(2);
    let mut v_config_6021_: *mut LeanObject = *_args.add(3);
    let mut v_pkg_6022_: *mut LeanObject = *_args.add(4);
    let mut v_shouldExport_6023_: *mut LeanObject = *_args.add(5);
    let mut v___x_6024_: *mut LeanObject = *_args.add(6);
    let mut v___x_6025_: *mut LeanObject = *_args.add(7);
    let mut v_dir_6026_: *mut LeanObject = *_args.add(8);
    let mut v_self_6027_: *mut LeanObject = *_args.add(9);
    let mut v___y_6028_: *mut LeanObject = *_args.add(10);
    let mut v___y_6029_: *mut LeanObject = *_args.add(11);
    let mut v___y_6030_: *mut LeanObject = *_args.add(12);
    let mut v___y_6031_: *mut LeanObject = *_args.add(13);
    let mut v___y_6032_: *mut LeanObject = *_args.add(14);
    let mut v___y_6033_: *mut LeanObject = *_args.add(15);
    let mut v___y_6034_: *mut LeanObject = *_args.add(16);
    let mut v_shouldExport_boxed_6035_: u8 = 0;
    let mut v___x_7352__boxed_6036_: u8 = 0;
    let mut v_res_6037_: *mut LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_6035_ = (lean_unbox(v_shouldExport_6023_) as u8);
    v___x_7352__boxed_6036_ = (lean_unbox(v___x_6024_) as u8);
    v_res_6037_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v___x_6018_, v___x_6019_, v_config_6020_, v_config_6021_, v_pkg_6022_, v_shouldExport_boxed_6035_, v___x_7352__boxed_6036_, v___x_6025_, v_dir_6026_, v_self_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
    lean_dec_ref(v___y_6032_);
    lean_dec(v___y_6031_);
    lean_dec(v___y_6030_);
    lean_dec(v___y_6029_);
    lean_dec(v_config_6021_);
    return v_res_6037_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(
    mut v___y_6038_: *mut LeanObject,
    mut v_self_6039_: *mut LeanObject,
    mut v_shouldExport_6040_: u8,
    mut v_a_6041_: *mut LeanObject,
    mut v_a_6042_: *mut LeanObject,
    mut v_a_6043_: *mut LeanObject,
    mut v_a_6044_: *mut LeanObject,
    mut v_a_6045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBuildConfig_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_registeredJobs_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_6049_: u8 = 0;
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: u8 = 0;
    let mut v___x_6052_: u8 = 0;
    let mut v___x_6053_: u8 = 0;
    let mut v___y_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6075_: u8 = 0;
    let mut v_task_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6080_: u8 = 0;
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: u8 = 0;
    let mut v_job_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6097_: u8 = 0;
    let mut v_unused_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBuildConfig_6047_ = lean_ctor_get(v_a_6044_, 0);
                v_registeredJobs_6048_ = lean_ctor_get(v_a_6044_, 3);
                v_verbosity_6049_ = lean_ctor_get_uint8(
                    v_toBuildConfig_6047_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                v___x_6050_ = l_Lake_instDataKindFilePath;
                v___x_6051_ = 2;
                v___x_6052_ = l_Lake_instDecidableEqVerbosity(v_verbosity_6049_, v___x_6051_);
                v___x_6053_ = 1;
                if v___x_6052_ == 0 {
                    v___x_6100_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0;
                    v___y_6055_ = v___x_6100_;
                    state = 1;
                    continue;
                } else {
                    if v_shouldExport_6040_ == 0 {
                        v___x_6101_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1;
                        v___y_6055_ = v___x_6101_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6102_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2;
                        v___y_6055_ = v___x_6102_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pkg_6056_ = lean_ctor_get(v_self_6039_, 0);
                lean_inc_ref_n(v_pkg_6056_, 2);
                v_name_6057_ = lean_ctor_get(v_self_6039_, 1);
                lean_inc_n(v_name_6057_, 2);
                v_config_6058_ = lean_ctor_get(v_self_6039_, 2);
                lean_inc(v_config_6058_);
                v_keyName_6059_ = lean_ctor_get(v_pkg_6056_, 2);
                v_dir_6060_ = lean_ctor_get(v_pkg_6056_, 4);
                lean_inc_ref(v_dir_6060_);
                v_config_6061_ = lean_ctor_get(v_pkg_6056_, 6);
                lean_inc_ref(v_config_6061_);
                v___x_6062_ = l_Lake_LeanLib_modulesFacet;
                lean_inc(v_keyName_6059_);
                v___x_6063_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_6063_, 0, v_keyName_6059_);
                lean_ctor_set(v___x_6063_, 1, v_name_6057_);
                v___x_6064_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
                lean_inc_ref(v_self_6039_);
                v___x_6065_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_6065_, 0, v___x_6063_);
                lean_ctor_set(v___x_6065_, 1, v___x_6064_);
                lean_ctor_set(v___x_6065_, 2, v_self_6039_);
                lean_ctor_set(v___x_6065_, 3, v___x_6062_);
                v___x_6066_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6066_, 0, v_pkg_6056_);
                v___x_6067_ = lean_box((v_shouldExport_6040_) as usize);
                v___x_6068_ = lean_box((v___x_6053_) as usize);
                v___f_6069_ = lean_alloc_closure(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed as *mut core::ffi::c_void, 17, 10);
                lean_closure_set(v___f_6069_, 0, v___x_6065_);
                lean_closure_set(v___f_6069_, 1, v___x_6066_);
                lean_closure_set(v___f_6069_, 2, v_config_6061_);
                lean_closure_set(v___f_6069_, 3, v_config_6058_);
                lean_closure_set(v___f_6069_, 4, v_pkg_6056_);
                lean_closure_set(v___f_6069_, 5, v___x_6067_);
                lean_closure_set(v___f_6069_, 6, v___x_6068_);
                lean_closure_set(v___f_6069_, 7, v___x_6050_);
                lean_closure_set(v___f_6069_, 8, v_dir_6060_);
                lean_closure_set(v___f_6069_, 9, v_self_6039_);
                v___x_6070_ = l_Lake_ensureJob___redArg(
                    v___x_6050_,
                    v___f_6069_,
                    v___y_6038_,
                    v_a_6041_,
                    v_a_6042_,
                    v_a_6043_,
                    v_a_6044_,
                    v_a_6045_,
                );
                if lean_obj_tag(v___x_6070_) == 0 {
                    v_a_6071_ = lean_ctor_get(v___x_6070_, 0);
                    v_a_6072_ = lean_ctor_get(v___x_6070_, 1);
                    v_isSharedCheck_6099_ = (!lean_is_exclusive(v___x_6070_)) as u8;
                    if v_isSharedCheck_6099_ == 0 {
                        v___x_6074_ = v___x_6070_;
                        v_isShared_6075_ = v_isSharedCheck_6099_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6072_);
                        lean_inc(v_a_6071_);
                        lean_dec(v___x_6070_);
                        v___x_6074_ = lean_box(0);
                        v_isShared_6075_ = v_isSharedCheck_6099_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_name_6057_);
                    return v___x_6070_;
                }
            }
            2 => {
                v_task_6076_ = lean_ctor_get(v_a_6071_, 0);
                v_kind_6077_ = lean_ctor_get(v_a_6071_, 1);
                v_isSharedCheck_6097_ = (!lean_is_exclusive(v_a_6071_)) as u8;
                if v_isSharedCheck_6097_ == 0 {
                    v_unused_6098_ = lean_ctor_get(v_a_6071_, 2);
                    lean_dec(v_unused_6098_);
                    v___x_6079_ = v_a_6071_;
                    v_isShared_6080_ = v_isSharedCheck_6097_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_kind_6077_);
                    lean_inc(v_task_6076_);
                    lean_dec(v_a_6071_);
                    v___x_6079_ = lean_box(0);
                    v_isShared_6080_ = v_isSharedCheck_6097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6081_ = lean_st_ref_take(v_registeredJobs_6048_);
                v___x_6082_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_6057_,
                    v___x_6053_,
                );
                v___x_6083_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0;
                v___x_6084_ = lean_string_append(v___x_6082_, v___x_6083_);
                v___x_6085_ = lean_string_append(v___x_6084_, v___y_6055_);
                v___x_6086_ = 0;
                if v_isShared_6080_ == 0 {
                    lean_ctor_set(v___x_6079_, 2, v___x_6085_);
                    v_job_6088_ = v___x_6079_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6096_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6096_, 0, v_task_6076_);
                    lean_ctor_set(v_reuseFailAlloc_6096_, 1, v_kind_6077_);
                    lean_ctor_set(v_reuseFailAlloc_6096_, 2, v___x_6085_);
                    v_job_6088_ = v_reuseFailAlloc_6096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v_job_6088_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6086_,
                );
                lean_inc_ref(v_job_6088_);
                v___x_6089_ = l_Lake_Job_toOpaque___redArg(v_job_6088_);
                v___x_6090_ = lean_array_push(v___x_6081_, v___x_6089_);
                v___x_6091_ = lean_st_ref_set(v_registeredJobs_6048_, v___x_6090_);
                v___x_6092_ = l_Lake_Job_renew___redArg(v_job_6088_);
                if v_isShared_6075_ == 0 {
                    lean_ctor_set(v___x_6074_, 0, v___x_6092_);
                    v___x_6094_ = v___x_6074_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6095_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6095_, 0, v___x_6092_);
                    lean_ctor_set(v_reuseFailAlloc_6095_, 1, v_a_6072_);
                    v___x_6094_ = v_reuseFailAlloc_6095_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(
    mut v___y_6103_: *mut LeanObject,
    mut v_self_6104_: *mut LeanObject,
    mut v_shouldExport_6105_: *mut LeanObject,
    mut v_a_6106_: *mut LeanObject,
    mut v_a_6107_: *mut LeanObject,
    mut v_a_6108_: *mut LeanObject,
    mut v_a_6109_: *mut LeanObject,
    mut v_a_6110_: *mut LeanObject,
    mut v_a_6111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldExport_boxed_6112_: u8 = 0;
    let mut v_res_6113_: *mut LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_6112_ = (lean_unbox(v_shouldExport_6105_) as u8);
    v_res_6113_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_6103_, v_self_6104_, v_shouldExport_boxed_6112_, v_a_6106_, v_a_6107_, v_a_6108_, v_a_6109_, v_a_6110_);
    lean_dec_ref(v_a_6109_);
    lean_dec(v_a_6108_);
    lean_dec(v_a_6107_);
    lean_dec(v_a_6106_);
    return v_res_6113_;
}
pub unsafe fn l_Lake_LeanLib_staticFacetConfig___lam__0(
    mut v_x_6114_: *mut LeanObject,
    mut v___y_6115_: *mut LeanObject,
    mut v___y_6116_: *mut LeanObject,
    mut v___y_6117_: *mut LeanObject,
    mut v___y_6118_: *mut LeanObject,
    mut v___y_6119_: *mut LeanObject,
    mut v___y_6120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6122_: u8 = 0;
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    v___x_6122_ = 0;
    v___x_6123_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_6115_, v_x_6114_, v___x_6122_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_);
    return v___x_6123_;
}
pub unsafe fn l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(
    mut v_x_6124_: *mut LeanObject,
    mut v___y_6125_: *mut LeanObject,
    mut v___y_6126_: *mut LeanObject,
    mut v___y_6127_: *mut LeanObject,
    mut v___y_6128_: *mut LeanObject,
    mut v___y_6129_: *mut LeanObject,
    mut v___y_6130_: *mut LeanObject,
    mut v___y_6131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6132_: *mut LeanObject = core::ptr::null_mut();
    v_res_6132_ = l_Lake_LeanLib_staticFacetConfig___lam__0(
        v_x_6124_,
        v___y_6125_,
        v___y_6126_,
        v___y_6127_,
        v___y_6128_,
        v___y_6129_,
        v___y_6130_,
    );
    lean_dec_ref(v___y_6129_);
    lean_dec(v___y_6128_);
    lean_dec(v___y_6127_);
    lean_dec(v___y_6126_);
    return v_res_6132_;
}
pub unsafe fn _init_l_Lake_LeanLib_staticFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___f_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: u8 = 0;
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut LeanObject = core::ptr::null_mut();
    v___f_6135_ = l_Lake_LeanLib_staticFacetConfig___closed__1;
    v___x_6136_ = 1;
    v___x_6137_ = l_Lake_instDataKindFilePath;
    v___f_6138_ = l_Lake_LeanLib_staticFacetConfig___closed__0;
    v___x_6139_ = l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
    v___x_6140_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_6140_, 0, v___x_6139_);
    lean_ctor_set(v___x_6140_, 1, v___f_6138_);
    lean_ctor_set(v___x_6140_, 2, v___x_6137_);
    lean_ctor_set(v___x_6140_, 3, v___f_6135_);
    lean_ctor_set_uint8(
        v___x_6140_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_6136_,
    );
    lean_ctor_set_uint8(
        v___x_6140_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_6136_,
    );
    return v___x_6140_;
}
pub unsafe fn _init_l_Lake_LeanLib_staticFacetConfig() -> *mut LeanObject {
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    v___x_6141_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_staticFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_staticFacetConfig___closed__2_once),
        _init_l_Lake_LeanLib_staticFacetConfig___closed__2,
    );
    return v___x_6141_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(
    mut v_a_6142_: *mut LeanObject,
    mut v_as_6143_: *mut LeanObject,
    mut v_i_6144_: usize,
    mut v_stop_6145_: usize,
    mut v_b_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    v___x_6154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_6142_, v_as_6143_, v_i_6144_, v_stop_6145_, v_b_6146_, v___y_6152_);
    return v___x_6154_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(
    mut v_a_6155_: *mut LeanObject,
    mut v_as_6156_: *mut LeanObject,
    mut v_i_6157_: *mut LeanObject,
    mut v_stop_6158_: *mut LeanObject,
    mut v_b_6159_: *mut LeanObject,
    mut v___y_6160_: *mut LeanObject,
    mut v___y_6161_: *mut LeanObject,
    mut v___y_6162_: *mut LeanObject,
    mut v___y_6163_: *mut LeanObject,
    mut v___y_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6167_: usize = 0;
    let mut v_stop_boxed_6168_: usize = 0;
    let mut v_res_6169_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6167_ = lean_unbox_usize(v_i_6157_);
    lean_dec(v_i_6157_);
    v_stop_boxed_6168_ = lean_unbox_usize(v_stop_6158_);
    lean_dec(v_stop_6158_);
    v_res_6169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_6155_, v_as_6156_, v_i_boxed_6167_, v_stop_boxed_6168_, v_b_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
    lean_dec_ref(v___y_6164_);
    lean_dec(v___y_6163_);
    lean_dec(v___y_6162_);
    lean_dec(v___y_6161_);
    lean_dec_ref(v___y_6160_);
    lean_dec_ref(v_as_6156_);
    lean_dec(v_a_6155_);
    return v_res_6169_;
}
pub unsafe fn l_Lake_LeanLib_staticExportFacetConfig___lam__0(
    mut v_x_6170_: *mut LeanObject,
    mut v___y_6171_: *mut LeanObject,
    mut v___y_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
    mut v___y_6174_: *mut LeanObject,
    mut v___y_6175_: *mut LeanObject,
    mut v___y_6176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6178_: u8 = 0;
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    v___x_6178_ = 1;
    v___x_6179_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_6171_, v_x_6170_, v___x_6178_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_);
    return v___x_6179_;
}
pub unsafe fn l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(
    mut v_x_6180_: *mut LeanObject,
    mut v___y_6181_: *mut LeanObject,
    mut v___y_6182_: *mut LeanObject,
    mut v___y_6183_: *mut LeanObject,
    mut v___y_6184_: *mut LeanObject,
    mut v___y_6185_: *mut LeanObject,
    mut v___y_6186_: *mut LeanObject,
    mut v___y_6187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6188_: *mut LeanObject = core::ptr::null_mut();
    v_res_6188_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(
        v_x_6180_,
        v___y_6181_,
        v___y_6182_,
        v___y_6183_,
        v___y_6184_,
        v___y_6185_,
        v___y_6186_,
    );
    lean_dec_ref(v___y_6185_);
    lean_dec(v___y_6184_);
    lean_dec(v___y_6183_);
    lean_dec(v___y_6182_);
    return v_res_6188_;
}
pub unsafe fn _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___f_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: u8 = 0;
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    v___f_6190_ = l_Lake_LeanLib_staticFacetConfig___closed__1;
    v___x_6191_ = 1;
    v___x_6192_ = l_Lake_instDataKindFilePath;
    v___f_6193_ = l_Lake_LeanLib_staticExportFacetConfig___closed__0;
    v___x_6194_ = l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
    v___x_6195_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_6195_, 0, v___x_6194_);
    lean_ctor_set(v___x_6195_, 1, v___f_6193_);
    lean_ctor_set(v___x_6195_, 2, v___x_6192_);
    lean_ctor_set(v___x_6195_, 3, v___f_6190_);
    lean_ctor_set_uint8(
        v___x_6195_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_6191_,
    );
    lean_ctor_set_uint8(
        v___x_6195_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_6191_,
    );
    return v___x_6195_;
}
pub unsafe fn _init_l_Lake_LeanLib_staticExportFacetConfig() -> *mut LeanObject {
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    v___x_6196_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_staticExportFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_staticExportFacetConfig___closed__1_once),
        _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1,
    );
    return v___x_6196_;
}
pub unsafe fn _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_6197_: u8 = 0;
    let mut v_name_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    v___x_6197_ = 1;
    v_name_6198_ = l_Lake_instDataKindDynlib;
    v___x_6199_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_6198_,
        v___x_6197_,
    );
    return v___x_6199_;
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(
    mut v_defaultPkg_6200_: *mut LeanObject,
    mut v_self_6201_: *mut LeanObject,
    mut v_a_6202_: *mut LeanObject,
    mut v_a_6203_: *mut LeanObject,
    mut v_a_6204_: *mut LeanObject,
    mut v_a_6205_: *mut LeanObject,
    mut v_a_6206_: *mut LeanObject,
    mut v_a_6207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6209_: u8 = 0;
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6215_: u8 = 0;
    let mut v_a_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6219_: u8 = 0;
    let mut v_kind_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: u8 = 0;
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: u8 = 0;
    let mut v___x_6242_: u8 = 0;
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6251_: u8 = 0;
    let mut v_unused_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6253_: u8 = 0;
    let mut v_unused_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6259_: u8 = 0;
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6209_ = 1;
                lean_inc_ref_n(v_self_6201_, 2);
                v___x_6210_ =
                    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
                        v_defaultPkg_6200_,
                        v_self_6201_,
                        v_self_6201_,
                        v___x_6209_,
                        v_a_6202_,
                        v_a_6203_,
                        v_a_6204_,
                        v_a_6205_,
                        v_a_6206_,
                        v_a_6207_,
                    );
                if lean_obj_tag(v___x_6210_) == 0 {
                    v_a_6211_ = lean_ctor_get(v___x_6210_, 0);
                    lean_inc(v_a_6211_);
                    v_snd_6212_ = lean_ctor_get(v_a_6211_, 1);
                    v_isSharedCheck_6253_ = (!lean_is_exclusive(v_a_6211_)) as u8;
                    if v_isSharedCheck_6253_ == 0 {
                        v_unused_6254_ = lean_ctor_get(v_a_6211_, 0);
                        lean_dec(v_unused_6254_);
                        v___x_6214_ = v_a_6211_;
                        v_isShared_6215_ = v_isSharedCheck_6253_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6212_);
                        lean_dec(v_a_6211_);
                        v___x_6214_ = lean_box(0);
                        v_isShared_6215_ = v_isSharedCheck_6253_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_self_6201_);
                    v_a_6255_ = lean_ctor_get(v___x_6210_, 0);
                    v_a_6256_ = lean_ctor_get(v___x_6210_, 1);
                    v_isSharedCheck_6263_ = (!lean_is_exclusive(v___x_6210_)) as u8;
                    if v_isSharedCheck_6263_ == 0 {
                        v___x_6258_ = v___x_6210_;
                        v_isShared_6259_ = v_isSharedCheck_6263_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6256_);
                        lean_inc(v_a_6255_);
                        lean_dec(v___x_6210_);
                        v___x_6258_ = lean_box(0);
                        v_isShared_6259_ = v_isSharedCheck_6263_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6216_ = lean_ctor_get(v___x_6210_, 1);
                v_isSharedCheck_6251_ = (!lean_is_exclusive(v___x_6210_)) as u8;
                if v_isSharedCheck_6251_ == 0 {
                    v_unused_6252_ = lean_ctor_get(v___x_6210_, 0);
                    lean_dec(v_unused_6252_);
                    v___x_6218_ = v___x_6210_;
                    v_isShared_6219_ = v_isSharedCheck_6251_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_6216_);
                    lean_dec(v___x_6210_);
                    v___x_6218_ = lean_box(0);
                    v_isShared_6219_ = v_isSharedCheck_6251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_kind_6220_ = lean_ctor_get(v_snd_6212_, 1);
                v_name_6221_ = l_Lake_instDataKindDynlib;
                v___x_6241_ = lean_name_eq(v_kind_6220_, v_name_6221_);
                if v___x_6241_ == 0 {
                    lean_inc(v_kind_6220_);
                    lean_del_object(v___x_6214_);
                    lean_dec(v_snd_6212_);
                    v___x_6242_ = l_Lean_Name_isAnonymous(v_kind_6220_);
                    if v___x_6242_ == 0 {
                        v___x_6243_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4;
                        v___x_6244_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_6220_,
                                v___x_6209_,
                            );
                        v___x_6245_ = lean_string_append(v___x_6243_, v___x_6244_);
                        lean_dec_ref(v___x_6244_);
                        v___x_6246_ = lean_string_append(v___x_6245_, v___x_6243_);
                        v___y_6223_ = v___x_6246_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_kind_6220_);
                        v___x_6247_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5;
                        v___y_6223_ = v___x_6247_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6218_);
                    lean_dec_ref(v_self_6201_);
                    if v_isShared_6215_ == 0 {
                        lean_ctor_set(v___x_6214_, 1, v_a_6216_);
                        lean_ctor_set(v___x_6214_, 0, v_snd_6212_);
                        v___x_6249_ = v___x_6214_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6250_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_snd_6212_);
                        lean_ctor_set(v_reuseFailAlloc_6250_, 1, v_a_6216_);
                        v___x_6249_ = v_reuseFailAlloc_6250_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6224_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0;
                v___x_6225_ = l_Lake_PartialBuildKey_toString(v_self_6201_);
                v___x_6226_ = lean_string_append(v___x_6224_, v___x_6225_);
                lean_dec_ref(v___x_6225_);
                v___x_6227_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1;
                v___x_6228_ = lean_string_append(v___x_6226_, v___x_6227_);
                v___x_6229_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once), _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
                v___x_6230_ = lean_string_append(v___x_6228_, v___x_6229_);
                v___x_6231_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3;
                v___x_6232_ = lean_string_append(v___x_6230_, v___x_6231_);
                v___x_6233_ = lean_string_append(v___x_6232_, v___y_6223_);
                lean_dec_ref(v___y_6223_);
                v___x_6234_ = 3;
                v___x_6235_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_6235_, 0, v___x_6233_);
                lean_ctor_set_uint8(
                    v___x_6235_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6234_,
                );
                v___x_6236_ = lean_array_get_size(v_a_6216_);
                v___x_6237_ = lean_array_push(v_a_6216_, v___x_6235_);
                if v_isShared_6219_ == 0 {
                    lean_ctor_set_tag(v___x_6218_, 1);
                    lean_ctor_set(v___x_6218_, 1, v___x_6237_);
                    lean_ctor_set(v___x_6218_, 0, v___x_6236_);
                    v___x_6239_ = v___x_6218_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 0, v___x_6236_);
                    lean_ctor_set(v_reuseFailAlloc_6240_, 1, v___x_6237_);
                    v___x_6239_ = v_reuseFailAlloc_6240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6239_;
            }
            5 => {
                return v___x_6249_;
            }
            6 => {
                if v_isShared_6259_ == 0 {
                    v___x_6261_ = v___x_6258_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6262_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6262_, 0, v_a_6255_);
                    lean_ctor_set(v_reuseFailAlloc_6262_, 1, v_a_6256_);
                    v___x_6261_ = v_reuseFailAlloc_6262_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(
    mut v_defaultPkg_6264_: *mut LeanObject,
    mut v_self_6265_: *mut LeanObject,
    mut v_a_6266_: *mut LeanObject,
    mut v_a_6267_: *mut LeanObject,
    mut v_a_6268_: *mut LeanObject,
    mut v_a_6269_: *mut LeanObject,
    mut v_a_6270_: *mut LeanObject,
    mut v_a_6271_: *mut LeanObject,
    mut v_a_6272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6273_: *mut LeanObject = core::ptr::null_mut();
    v_res_6273_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_6264_, v_self_6265_, v_a_6266_, v_a_6267_, v_a_6268_, v_a_6269_, v_a_6270_, v_a_6271_);
    lean_dec_ref(v_a_6270_);
    lean_dec(v_a_6269_);
    lean_dec(v_a_6268_);
    lean_dec(v_a_6267_);
    return v_res_6273_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    v___x_6276_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0;
    v___x_6277_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once
        ),
        _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2,
    );
    v___x_6278_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6278_, 0, v___x_6277_);
    lean_ctor_set(v___x_6278_, 1, v___x_6276_);
    return v___x_6278_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5()
-> *mut LeanObject {
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    v___x_6279_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
    return v___x_6279_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(
    mut v___x_6280_: *mut LeanObject,
    mut v_as_6281_: *mut LeanObject,
    mut v_i_6282_: usize,
    mut v_stop_6283_: usize,
    mut v_b_6284_: *mut LeanObject,
    mut v___y_6285_: *mut LeanObject,
    mut v___y_6286_: *mut LeanObject,
    mut v___y_6287_: *mut LeanObject,
    mut v___y_6288_: *mut LeanObject,
    mut v___y_6289_: *mut LeanObject,
    mut v___y_6290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6292_: u8 = 0;
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: usize = 0;
    let mut v___x_6299_: usize = 0;
    let mut v_a_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6305_: u8 = 0;
    let mut v___x_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6309_: u8 = 0;
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6292_ = lean_usize_dec_eq(v_i_6282_, v_stop_6283_);
                if v___x_6292_ == 0 {
                    v___x_6293_ = lean_array_uget_borrowed(v_as_6281_, v_i_6282_);
                    lean_inc_ref(v___y_6285_);
                    lean_inc(v___x_6293_);
                    lean_inc_ref(v___x_6280_);
                    v___x_6294_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_6280_, v___x_6293_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_);
                    if lean_obj_tag(v___x_6294_) == 0 {
                        v_a_6295_ = lean_ctor_get(v___x_6294_, 0);
                        lean_inc(v_a_6295_);
                        v_a_6296_ = lean_ctor_get(v___x_6294_, 1);
                        lean_inc(v_a_6296_);
                        lean_dec_ref_known(v___x_6294_, 2);
                        v___x_6297_ = lean_array_push(v_b_6284_, v_a_6295_);
                        v___x_6298_ = 1usize;
                        v___x_6299_ = lean_usize_add(v_i_6282_, v___x_6298_);
                        v_i_6282_ = v___x_6299_;
                        v_b_6284_ = v___x_6297_;
                        v___y_6290_ = v_a_6296_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_6285_);
                        lean_dec_ref(v_b_6284_);
                        lean_dec_ref(v___x_6280_);
                        v_a_6301_ = lean_ctor_get(v___x_6294_, 0);
                        v_a_6302_ = lean_ctor_get(v___x_6294_, 1);
                        v_isSharedCheck_6309_ = (!lean_is_exclusive(v___x_6294_)) as u8;
                        if v_isSharedCheck_6309_ == 0 {
                            v___x_6304_ = v___x_6294_;
                            v_isShared_6305_ = v_isSharedCheck_6309_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6302_);
                            lean_inc(v_a_6301_);
                            lean_dec(v___x_6294_);
                            v___x_6304_ = lean_box(0);
                            v_isShared_6305_ = v_isSharedCheck_6309_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6285_);
                    lean_dec_ref(v___x_6280_);
                    v___x_6310_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6310_, 0, v_b_6284_);
                    lean_ctor_set(v___x_6310_, 1, v___y_6290_);
                    return v___x_6310_;
                }
            }
            1 => {
                if v_isShared_6305_ == 0 {
                    v___x_6307_ = v___x_6304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6308_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6308_, 0, v_a_6301_);
                    lean_ctor_set(v_reuseFailAlloc_6308_, 1, v_a_6302_);
                    v___x_6307_ = v_reuseFailAlloc_6308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(
    mut v___x_6311_: *mut LeanObject,
    mut v_as_6312_: *mut LeanObject,
    mut v_i_6313_: *mut LeanObject,
    mut v_stop_6314_: *mut LeanObject,
    mut v_b_6315_: *mut LeanObject,
    mut v___y_6316_: *mut LeanObject,
    mut v___y_6317_: *mut LeanObject,
    mut v___y_6318_: *mut LeanObject,
    mut v___y_6319_: *mut LeanObject,
    mut v___y_6320_: *mut LeanObject,
    mut v___y_6321_: *mut LeanObject,
    mut v___y_6322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6323_: usize = 0;
    let mut v_stop_boxed_6324_: usize = 0;
    let mut v_res_6325_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6323_ = lean_unbox_usize(v_i_6313_);
    lean_dec(v_i_6313_);
    v_stop_boxed_6324_ = lean_unbox_usize(v_stop_6314_);
    lean_dec(v_stop_6314_);
    v_res_6325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_6311_, v_as_6312_, v_i_boxed_6323_, v_stop_boxed_6324_, v_b_6315_, v___y_6316_, v___y_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_);
    lean_dec_ref(v___y_6320_);
    lean_dec(v___y_6319_);
    lean_dec(v___y_6318_);
    lean_dec(v___y_6317_);
    lean_dec_ref(v_as_6312_);
    return v_res_6325_;
}
pub unsafe fn l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(
    mut v_self_6326_: *mut LeanObject,
    mut v_a_6327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toHashSet_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toArray_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: u8 = 0;
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6333_: u8 = 0;
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v_unused_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toHashSet_6328_ = lean_ctor_get(v_self_6326_, 0);
                v_toArray_6329_ = lean_ctor_get(v_self_6326_, 1);
                v___x_6330_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_6328_, v_a_6327_);
                if v___x_6330_ == 0 {
                    lean_inc_ref(v_toArray_6329_);
                    lean_inc_ref(v_toHashSet_6328_);
                    v_isSharedCheck_6340_ = (!lean_is_exclusive(v_self_6326_)) as u8;
                    if v_isSharedCheck_6340_ == 0 {
                        v_unused_6341_ = lean_ctor_get(v_self_6326_, 1);
                        lean_dec(v_unused_6341_);
                        v_unused_6342_ = lean_ctor_get(v_self_6326_, 0);
                        lean_dec(v_unused_6342_);
                        v___x_6332_ = v_self_6326_;
                        v_isShared_6333_ = v_isSharedCheck_6340_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_self_6326_);
                        v___x_6332_ = lean_box(0);
                        v_isShared_6333_ = v_isSharedCheck_6340_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_6327_);
                    return v_self_6326_;
                }
            }
            1 => {
                v___x_6334_ = lean_box(0);
                lean_inc_ref(v_a_6327_);
                v___x_6335_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_6328_, v_a_6327_, v___x_6334_);
                v___x_6336_ = lean_array_push(v_toArray_6329_, v_a_6327_);
                if v_isShared_6333_ == 0 {
                    lean_ctor_set(v___x_6332_, 1, v___x_6336_);
                    lean_ctor_set(v___x_6332_, 0, v___x_6335_);
                    v___x_6338_ = v___x_6332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6339_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6339_, 0, v___x_6335_);
                    lean_ctor_set(v_reuseFailAlloc_6339_, 1, v___x_6336_);
                    v___x_6338_ = v_reuseFailAlloc_6339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(
    mut v_as_6343_: *mut LeanObject,
    mut v_i_6344_: usize,
    mut v_stop_6345_: usize,
    mut v_b_6346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6347_: u8 = 0;
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: usize = 0;
    let mut v___x_6351_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6347_ = lean_usize_dec_eq(v_i_6344_, v_stop_6345_);
                if v___x_6347_ == 0 {
                    v___x_6348_ = lean_array_uget_borrowed(v_as_6343_, v_i_6344_);
                    lean_inc(v___x_6348_);
                    v___x_6349_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_6346_, v___x_6348_);
                    v___x_6350_ = 1usize;
                    v___x_6351_ = lean_usize_add(v_i_6344_, v___x_6350_);
                    v_i_6344_ = v___x_6351_;
                    v_b_6346_ = v___x_6349_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6346_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(
    mut v_as_6353_: *mut LeanObject,
    mut v_i_6354_: *mut LeanObject,
    mut v_stop_6355_: *mut LeanObject,
    mut v_b_6356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6357_: usize = 0;
    let mut v_stop_boxed_6358_: usize = 0;
    let mut v_res_6359_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6357_ = lean_unbox_usize(v_i_6354_);
    lean_dec(v_i_6354_);
    v_stop_boxed_6358_ = lean_unbox_usize(v_stop_6355_);
    lean_dec(v_stop_6355_);
    v_res_6359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_6353_, v_i_boxed_6357_, v_stop_boxed_6358_, v_b_6356_);
    lean_dec_ref(v_as_6353_);
    return v_res_6359_;
}
pub unsafe fn l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(
    mut v_self_6360_: *mut LeanObject,
    mut v_arr_6361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: u8 = 0;
    v___x_6362_ = lean_unsigned_to_nat(0);
    v___x_6363_ = lean_array_get_size(v_arr_6361_);
    v___x_6364_ = lean_nat_dec_lt(v___x_6362_, v___x_6363_);
    if v___x_6364_ == 0 {
        return v_self_6360_;
    } else {
        let mut v___x_6365_: u8 = 0;
        v___x_6365_ = lean_nat_dec_le(v___x_6363_, v___x_6363_);
        if v___x_6365_ == 0 {
            if v___x_6364_ == 0 {
                return v_self_6360_;
            } else {
                let mut v___x_6366_: usize = 0;
                let mut v___x_6367_: usize = 0;
                let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
                v___x_6366_ = 0usize;
                v___x_6367_ = lean_usize_of_nat(v___x_6363_);
                v___x_6368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_6361_, v___x_6366_, v___x_6367_, v_self_6360_);
                return v___x_6368_;
            }
        } else {
            let mut v___x_6369_: usize = 0;
            let mut v___x_6370_: usize = 0;
            let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
            v___x_6369_ = 0usize;
            v___x_6370_ = lean_usize_of_nat(v___x_6363_);
            v___x_6371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_6361_, v___x_6369_, v___x_6370_, v_self_6360_);
            return v___x_6371_;
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(
    mut v_self_6372_: *mut LeanObject,
    mut v_arr_6373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6374_: *mut LeanObject = core::ptr::null_mut();
    v_res_6374_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_6372_, v_arr_6373_);
    lean_dec_ref(v_arr_6373_);
    return v_res_6374_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(
    mut v_as_6375_: *mut LeanObject,
    mut v_i_6376_: usize,
    mut v_stop_6377_: usize,
    mut v_b_6378_: *mut LeanObject,
    mut v___y_6379_: *mut LeanObject,
    mut v___y_6380_: *mut LeanObject,
    mut v___y_6381_: *mut LeanObject,
    mut v___y_6382_: *mut LeanObject,
    mut v___y_6383_: *mut LeanObject,
    mut v___y_6384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6386_: u8 = 0;
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: usize = 0;
    let mut v___x_6404_: usize = 0;
    let mut v_a_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6410_: u8 = 0;
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6414_: u8 = 0;
    let mut v_a_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6419_: u8 = 0;
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6423_: u8 = 0;
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6386_ = lean_usize_dec_eq(v_i_6376_, v_stop_6377_);
                if v___x_6386_ == 0 {
                    v___x_6387_ = lean_array_uget_borrowed(v_as_6375_, v_i_6376_);
                    v_lib_6388_ = lean_ctor_get(v___x_6387_, 0);
                    v_pkg_6389_ = lean_ctor_get(v_lib_6388_, 0);
                    v_name_6390_ = lean_ctor_get(v___x_6387_, 1);
                    v_keyName_6391_ = lean_ctor_get(v_pkg_6389_, 2);
                    v___x_6392_ = l_Lake_Module_transImportsFacet;
                    lean_inc(v_name_6390_);
                    lean_inc(v_keyName_6391_);
                    v___x_6393_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6393_, 0, v_keyName_6391_);
                    lean_ctor_set(v___x_6393_, 1, v_name_6390_);
                    v___x_6394_ = l_Lake_Module_keyword;
                    lean_inc(v___x_6387_);
                    v___x_6395_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v___x_6395_, 0, v___x_6393_);
                    lean_ctor_set(v___x_6395_, 1, v___x_6394_);
                    lean_ctor_set(v___x_6395_, 2, v___x_6387_);
                    lean_ctor_set(v___x_6395_, 3, v___x_6392_);
                    lean_inc_ref(v___y_6379_);
                    lean_inc_ref(v___y_6383_);
                    lean_inc(v___y_6382_);
                    lean_inc(v___y_6381_);
                    lean_inc(v___y_6380_);
                    v___x_6396_ = lean_apply_7(
                        v___y_6379_,
                        v___x_6395_,
                        v___y_6380_,
                        v___y_6381_,
                        v___y_6382_,
                        v___y_6383_,
                        v___y_6384_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_6396_) == 0 {
                        v_a_6397_ = lean_ctor_get(v___x_6396_, 0);
                        lean_inc(v_a_6397_);
                        v_a_6398_ = lean_ctor_get(v___x_6396_, 1);
                        lean_inc(v_a_6398_);
                        lean_dec_ref_known(v___x_6396_, 2);
                        v___x_6399_ = l_Lake_Job_await___redArg(v_a_6397_, v_a_6398_);
                        if lean_obj_tag(v___x_6399_) == 0 {
                            v_a_6400_ = lean_ctor_get(v___x_6399_, 0);
                            lean_inc(v_a_6400_);
                            v_a_6401_ = lean_ctor_get(v___x_6399_, 1);
                            lean_inc(v_a_6401_);
                            lean_dec_ref_known(v___x_6399_, 2);
                            v___x_6402_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_6378_, v_a_6400_);
                            lean_dec(v_a_6400_);
                            v___x_6403_ = 1usize;
                            v___x_6404_ = lean_usize_add(v_i_6376_, v___x_6403_);
                            v_i_6376_ = v___x_6404_;
                            v_b_6378_ = v___x_6402_;
                            v___y_6384_ = v_a_6401_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v___y_6379_);
                            lean_dec_ref(v_b_6378_);
                            v_a_6406_ = lean_ctor_get(v___x_6399_, 0);
                            v_a_6407_ = lean_ctor_get(v___x_6399_, 1);
                            v_isSharedCheck_6414_ = (!lean_is_exclusive(v___x_6399_)) as u8;
                            if v_isSharedCheck_6414_ == 0 {
                                v___x_6409_ = v___x_6399_;
                                v_isShared_6410_ = v_isSharedCheck_6414_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6407_);
                                lean_inc(v_a_6406_);
                                lean_dec(v___x_6399_);
                                v___x_6409_ = lean_box(0);
                                v_isShared_6410_ = v_isSharedCheck_6414_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_6379_);
                        lean_dec_ref(v_b_6378_);
                        v_a_6415_ = lean_ctor_get(v___x_6396_, 0);
                        v_a_6416_ = lean_ctor_get(v___x_6396_, 1);
                        v_isSharedCheck_6423_ = (!lean_is_exclusive(v___x_6396_)) as u8;
                        if v_isSharedCheck_6423_ == 0 {
                            v___x_6418_ = v___x_6396_;
                            v_isShared_6419_ = v_isSharedCheck_6423_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6416_);
                            lean_inc(v_a_6415_);
                            lean_dec(v___x_6396_);
                            v___x_6418_ = lean_box(0);
                            v_isShared_6419_ = v_isSharedCheck_6423_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6379_);
                    v___x_6424_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6424_, 0, v_b_6378_);
                    lean_ctor_set(v___x_6424_, 1, v___y_6384_);
                    return v___x_6424_;
                }
            }
            1 => {
                if v_isShared_6410_ == 0 {
                    v___x_6412_ = v___x_6409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6413_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_a_6406_);
                    lean_ctor_set(v_reuseFailAlloc_6413_, 1, v_a_6407_);
                    v___x_6412_ = v_reuseFailAlloc_6413_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6412_;
            }
            3 => {
                if v_isShared_6419_ == 0 {
                    v___x_6421_ = v___x_6418_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6422_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6422_, 0, v_a_6415_);
                    lean_ctor_set(v_reuseFailAlloc_6422_, 1, v_a_6416_);
                    v___x_6421_ = v_reuseFailAlloc_6422_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(
    mut v_as_6425_: *mut LeanObject,
    mut v_i_6426_: *mut LeanObject,
    mut v_stop_6427_: *mut LeanObject,
    mut v_b_6428_: *mut LeanObject,
    mut v___y_6429_: *mut LeanObject,
    mut v___y_6430_: *mut LeanObject,
    mut v___y_6431_: *mut LeanObject,
    mut v___y_6432_: *mut LeanObject,
    mut v___y_6433_: *mut LeanObject,
    mut v___y_6434_: *mut LeanObject,
    mut v___y_6435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6436_: usize = 0;
    let mut v_stop_boxed_6437_: usize = 0;
    let mut v_res_6438_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6436_ = lean_unbox_usize(v_i_6426_);
    lean_dec(v_i_6426_);
    v_stop_boxed_6437_ = lean_unbox_usize(v_stop_6427_);
    lean_dec(v_stop_6427_);
    v_res_6438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_6425_, v_i_boxed_6436_, v_stop_boxed_6437_, v_b_6428_, v___y_6429_, v___y_6430_, v___y_6431_, v___y_6432_, v___y_6433_, v___y_6434_);
    lean_dec_ref(v___y_6433_);
    lean_dec(v___y_6432_);
    lean_dec(v___y_6431_);
    lean_dec(v___y_6430_);
    lean_dec_ref(v_as_6425_);
    return v_res_6438_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(
    mut v_as_6439_: *mut LeanObject,
    mut v_i_6440_: usize,
    mut v_stop_6441_: usize,
    mut v_b_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
    mut v___y_6448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6450_: u8 = 0;
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: usize = 0;
    let mut v___x_6464_: usize = 0;
    let mut v_a_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6470_: u8 = 0;
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6474_: u8 = 0;
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6450_ = lean_usize_dec_eq(v_i_6440_, v_stop_6441_);
                if v___x_6450_ == 0 {
                    v___x_6451_ = lean_array_uget_borrowed(v_as_6439_, v_i_6440_);
                    v_pkg_6452_ = lean_ctor_get(v___x_6451_, 0);
                    v_name_6453_ = lean_ctor_get(v___x_6451_, 1);
                    v_keyName_6454_ = lean_ctor_get(v_pkg_6452_, 2);
                    v___x_6455_ = l_Lake_ExternLib_dynlibFacet;
                    lean_inc(v_name_6453_);
                    lean_inc(v_keyName_6454_);
                    v___x_6456_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v___x_6456_, 0, v_keyName_6454_);
                    lean_ctor_set(v___x_6456_, 1, v_name_6453_);
                    v___x_6457_ = l_Lake_ExternLib_keyword;
                    lean_inc(v___x_6451_);
                    v___x_6458_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v___x_6458_, 0, v___x_6456_);
                    lean_ctor_set(v___x_6458_, 1, v___x_6457_);
                    lean_ctor_set(v___x_6458_, 2, v___x_6451_);
                    lean_ctor_set(v___x_6458_, 3, v___x_6455_);
                    lean_inc_ref(v___y_6443_);
                    lean_inc_ref(v___y_6447_);
                    lean_inc(v___y_6446_);
                    lean_inc(v___y_6445_);
                    lean_inc(v___y_6444_);
                    v___x_6459_ = lean_apply_7(
                        v___y_6443_,
                        v___x_6458_,
                        v___y_6444_,
                        v___y_6445_,
                        v___y_6446_,
                        v___y_6447_,
                        v___y_6448_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_6459_) == 0 {
                        v_a_6460_ = lean_ctor_get(v___x_6459_, 0);
                        lean_inc(v_a_6460_);
                        v_a_6461_ = lean_ctor_get(v___x_6459_, 1);
                        lean_inc(v_a_6461_);
                        lean_dec_ref_known(v___x_6459_, 2);
                        v___x_6462_ = lean_array_push(v_b_6442_, v_a_6460_);
                        v___x_6463_ = 1usize;
                        v___x_6464_ = lean_usize_add(v_i_6440_, v___x_6463_);
                        v_i_6440_ = v___x_6464_;
                        v_b_6442_ = v___x_6462_;
                        v___y_6448_ = v_a_6461_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_6443_);
                        lean_dec_ref(v_b_6442_);
                        v_a_6466_ = lean_ctor_get(v___x_6459_, 0);
                        v_a_6467_ = lean_ctor_get(v___x_6459_, 1);
                        v_isSharedCheck_6474_ = (!lean_is_exclusive(v___x_6459_)) as u8;
                        if v_isSharedCheck_6474_ == 0 {
                            v___x_6469_ = v___x_6459_;
                            v_isShared_6470_ = v_isSharedCheck_6474_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6467_);
                            lean_inc(v_a_6466_);
                            lean_dec(v___x_6459_);
                            v___x_6469_ = lean_box(0);
                            v_isShared_6470_ = v_isSharedCheck_6474_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6443_);
                    v___x_6475_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6475_, 0, v_b_6442_);
                    lean_ctor_set(v___x_6475_, 1, v___y_6448_);
                    return v___x_6475_;
                }
            }
            1 => {
                if v_isShared_6470_ == 0 {
                    v___x_6472_ = v___x_6469_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6473_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_a_6466_);
                    lean_ctor_set(v_reuseFailAlloc_6473_, 1, v_a_6467_);
                    v___x_6472_ = v_reuseFailAlloc_6473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(
    mut v_as_6476_: *mut LeanObject,
    mut v_i_6477_: *mut LeanObject,
    mut v_stop_6478_: *mut LeanObject,
    mut v_b_6479_: *mut LeanObject,
    mut v___y_6480_: *mut LeanObject,
    mut v___y_6481_: *mut LeanObject,
    mut v___y_6482_: *mut LeanObject,
    mut v___y_6483_: *mut LeanObject,
    mut v___y_6484_: *mut LeanObject,
    mut v___y_6485_: *mut LeanObject,
    mut v___y_6486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6487_: usize = 0;
    let mut v_stop_boxed_6488_: usize = 0;
    let mut v_res_6489_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6487_ = lean_unbox_usize(v_i_6477_);
    lean_dec(v_i_6477_);
    v_stop_boxed_6488_ = lean_unbox_usize(v_stop_6478_);
    lean_dec(v_stop_6478_);
    v_res_6489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_6476_, v_i_boxed_6487_, v_stop_boxed_6488_, v_b_6479_, v___y_6480_, v___y_6481_, v___y_6482_, v___y_6483_, v___y_6484_, v___y_6485_);
    lean_dec_ref(v___y_6484_);
    lean_dec(v___y_6483_);
    lean_dec(v___y_6482_);
    lean_dec(v___y_6481_);
    lean_dec_ref(v_as_6476_);
    return v_res_6489_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(
    mut v_as_6490_: *mut LeanObject,
    mut v_i_6491_: usize,
    mut v_stop_6492_: usize,
    mut v_b_6493_: *mut LeanObject,
    mut v___y_6494_: *mut LeanObject,
    mut v___y_6495_: *mut LeanObject,
    mut v___y_6496_: *mut LeanObject,
    mut v___y_6497_: *mut LeanObject,
    mut v___y_6498_: *mut LeanObject,
    mut v___y_6499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: usize = 0;
    let mut v___x_6505_: usize = 0;
    let mut v___x_6507_: u8 = 0;
    let mut v_fst_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6514_: u8 = 0;
    let mut v_pkg_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: u8 = 0;
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6520_: u8 = 0;
    let mut v_keyName_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6539_: u8 = 0;
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6543_: u8 = 0;
    let mut v_reuseFailAlloc_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6545_: u8 = 0;
    let mut v_unused_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6548_: u8 = 0;
    let mut v_unused_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6507_ = lean_usize_dec_eq(v_i_6491_, v_stop_6492_);
                if v___x_6507_ == 0 {
                    v_fst_6508_ = lean_ctor_get(v_b_6493_, 0);
                    v_snd_6509_ = lean_ctor_get(v_b_6493_, 1);
                    v___x_6510_ = lean_array_uget(v_as_6490_, v_i_6491_);
                    v_lib_6511_ = lean_ctor_get(v___x_6510_, 0);
                    v_isSharedCheck_6548_ = (!lean_is_exclusive(v___x_6510_)) as u8;
                    if v_isSharedCheck_6548_ == 0 {
                        v_unused_6549_ = lean_ctor_get(v___x_6510_, 1);
                        lean_dec(v_unused_6549_);
                        v___x_6513_ = v___x_6510_;
                        v_isShared_6514_ = v_isSharedCheck_6548_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_lib_6511_);
                        lean_dec(v___x_6510_);
                        v___x_6513_ = lean_box(0);
                        v_isShared_6514_ = v_isSharedCheck_6548_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_6494_);
                    v___x_6550_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6550_, 0, v_b_6493_);
                    lean_ctor_set(v___x_6550_, 1, v___y_6499_);
                    return v___x_6550_;
                }
            }
            1 => {
                v___x_6504_ = 1usize;
                v___x_6505_ = lean_usize_add(v_i_6491_, v___x_6504_);
                v_i_6491_ = v___x_6505_;
                v_b_6493_ = v_a_6502_;
                v___y_6499_ = v_a_6503_;
                state = 0;
                continue;
            }
            2 => {
                v_pkg_6515_ = lean_ctor_get(v_lib_6511_, 0);
                v_name_6516_ = lean_ctor_get(v_lib_6511_, 1);
                lean_inc(v_name_6516_);
                v___x_6517_ = l_Lean_NameSet_contains(v_fst_6508_, v_name_6516_);
                if v___x_6517_ == 0 {
                    lean_inc(v_snd_6509_);
                    lean_inc(v_fst_6508_);
                    v_isSharedCheck_6545_ = (!lean_is_exclusive(v_b_6493_)) as u8;
                    if v_isSharedCheck_6545_ == 0 {
                        v_unused_6546_ = lean_ctor_get(v_b_6493_, 1);
                        lean_dec(v_unused_6546_);
                        v_unused_6547_ = lean_ctor_get(v_b_6493_, 0);
                        lean_dec(v_unused_6547_);
                        v___x_6519_ = v_b_6493_;
                        v_isShared_6520_ = v_isSharedCheck_6545_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_b_6493_);
                        v___x_6519_ = lean_box(0);
                        v_isShared_6520_ = v_isSharedCheck_6545_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_name_6516_);
                    lean_del_object(v___x_6513_);
                    lean_dec_ref(v_lib_6511_);
                    v_a_6502_ = v_b_6493_;
                    v_a_6503_ = v___y_6499_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_keyName_6521_ = lean_ctor_get(v_pkg_6515_, 2);
                v___x_6522_ = l_Lake_LeanLib_sharedFacet;
                lean_inc(v_name_6516_);
                lean_inc(v_keyName_6521_);
                if v_isShared_6514_ == 0 {
                    lean_ctor_set_tag(v___x_6513_, 3);
                    lean_ctor_set(v___x_6513_, 1, v_name_6516_);
                    lean_ctor_set(v___x_6513_, 0, v_keyName_6521_);
                    v___x_6524_ = v___x_6513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6544_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6544_, 0, v_keyName_6521_);
                    lean_ctor_set(v_reuseFailAlloc_6544_, 1, v_name_6516_);
                    v___x_6524_ = v_reuseFailAlloc_6544_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6525_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
                v___x_6526_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_6526_, 0, v___x_6524_);
                lean_ctor_set(v___x_6526_, 1, v___x_6525_);
                lean_ctor_set(v___x_6526_, 2, v_lib_6511_);
                lean_ctor_set(v___x_6526_, 3, v___x_6522_);
                lean_inc_ref(v___y_6494_);
                lean_inc_ref(v___y_6498_);
                lean_inc(v___y_6497_);
                lean_inc(v___y_6496_);
                lean_inc(v___y_6495_);
                v___x_6527_ = lean_apply_7(
                    v___y_6494_,
                    v___x_6526_,
                    v___y_6495_,
                    v___y_6496_,
                    v___y_6497_,
                    v___y_6498_,
                    v___y_6499_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6527_) == 0 {
                    v_a_6528_ = lean_ctor_get(v___x_6527_, 0);
                    lean_inc(v_a_6528_);
                    v_a_6529_ = lean_ctor_get(v___x_6527_, 1);
                    lean_inc(v_a_6529_);
                    lean_dec_ref_known(v___x_6527_, 2);
                    v___x_6530_ = lean_array_push(v_snd_6509_, v_a_6528_);
                    v___x_6531_ = l_Lean_NameSet_insert(v_fst_6508_, v_name_6516_);
                    if v_isShared_6520_ == 0 {
                        lean_ctor_set(v___x_6519_, 1, v___x_6530_);
                        lean_ctor_set(v___x_6519_, 0, v___x_6531_);
                        v___x_6533_ = v___x_6519_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6534_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6534_, 0, v___x_6531_);
                        lean_ctor_set(v_reuseFailAlloc_6534_, 1, v___x_6530_);
                        v___x_6533_ = v_reuseFailAlloc_6534_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6519_);
                    lean_dec(v_name_6516_);
                    lean_dec(v_snd_6509_);
                    lean_dec(v_fst_6508_);
                    lean_dec_ref(v___y_6494_);
                    v_a_6535_ = lean_ctor_get(v___x_6527_, 0);
                    v_a_6536_ = lean_ctor_get(v___x_6527_, 1);
                    v_isSharedCheck_6543_ = (!lean_is_exclusive(v___x_6527_)) as u8;
                    if v_isSharedCheck_6543_ == 0 {
                        v___x_6538_ = v___x_6527_;
                        v_isShared_6539_ = v_isSharedCheck_6543_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6536_);
                        lean_inc(v_a_6535_);
                        lean_dec(v___x_6527_);
                        v___x_6538_ = lean_box(0);
                        v_isShared_6539_ = v_isSharedCheck_6543_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_a_6502_ = v___x_6533_;
                v_a_6503_ = v_a_6529_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_6539_ == 0 {
                    v___x_6541_ = v___x_6538_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6542_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6542_, 0, v_a_6535_);
                    lean_ctor_set(v_reuseFailAlloc_6542_, 1, v_a_6536_);
                    v___x_6541_ = v_reuseFailAlloc_6542_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(
    mut v_as_6551_: *mut LeanObject,
    mut v_i_6552_: *mut LeanObject,
    mut v_stop_6553_: *mut LeanObject,
    mut v_b_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
    mut v___y_6556_: *mut LeanObject,
    mut v___y_6557_: *mut LeanObject,
    mut v___y_6558_: *mut LeanObject,
    mut v___y_6559_: *mut LeanObject,
    mut v___y_6560_: *mut LeanObject,
    mut v___y_6561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6562_: usize = 0;
    let mut v_stop_boxed_6563_: usize = 0;
    let mut v_res_6564_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6562_ = lean_unbox_usize(v_i_6552_);
    lean_dec(v_i_6552_);
    v_stop_boxed_6563_ = lean_unbox_usize(v_stop_6553_);
    lean_dec(v_stop_6553_);
    v_res_6564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_6551_, v_i_boxed_6562_, v_stop_boxed_6563_, v_b_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
    lean_dec_ref(v___y_6559_);
    lean_dec(v___y_6558_);
    lean_dec(v___y_6557_);
    lean_dec(v___y_6556_);
    lean_dec_ref(v_as_6551_);
    return v_res_6564_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(
    mut v___x_6565_: *mut LeanObject,
    mut v_as_6566_: *mut LeanObject,
    mut v_i_6567_: usize,
    mut v_stop_6568_: usize,
    mut v_b_6569_: *mut LeanObject,
    mut v___y_6570_: *mut LeanObject,
    mut v___y_6571_: *mut LeanObject,
    mut v___y_6572_: *mut LeanObject,
    mut v___y_6573_: *mut LeanObject,
    mut v___y_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6577_: u8 = 0;
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: usize = 0;
    let mut v___x_6584_: usize = 0;
    let mut v_a_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6590_: u8 = 0;
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6594_: u8 = 0;
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6577_ = lean_usize_dec_eq(v_i_6567_, v_stop_6568_);
                if v___x_6577_ == 0 {
                    v___x_6578_ = lean_array_uget_borrowed(v_as_6566_, v_i_6567_);
                    lean_inc_ref(v___y_6570_);
                    lean_inc(v___x_6578_);
                    lean_inc_ref(v___x_6565_);
                    v___x_6579_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_6565_, v___x_6578_, v___y_6570_, v___y_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_);
                    if lean_obj_tag(v___x_6579_) == 0 {
                        v_a_6580_ = lean_ctor_get(v___x_6579_, 0);
                        lean_inc(v_a_6580_);
                        v_a_6581_ = lean_ctor_get(v___x_6579_, 1);
                        lean_inc(v_a_6581_);
                        lean_dec_ref_known(v___x_6579_, 2);
                        v___x_6582_ = lean_array_push(v_b_6569_, v_a_6580_);
                        v___x_6583_ = 1usize;
                        v___x_6584_ = lean_usize_add(v_i_6567_, v___x_6583_);
                        v_i_6567_ = v___x_6584_;
                        v_b_6569_ = v___x_6582_;
                        v___y_6575_ = v_a_6581_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_6570_);
                        lean_dec_ref(v_b_6569_);
                        lean_dec_ref(v___x_6565_);
                        v_a_6586_ = lean_ctor_get(v___x_6579_, 0);
                        v_a_6587_ = lean_ctor_get(v___x_6579_, 1);
                        v_isSharedCheck_6594_ = (!lean_is_exclusive(v___x_6579_)) as u8;
                        if v_isSharedCheck_6594_ == 0 {
                            v___x_6589_ = v___x_6579_;
                            v_isShared_6590_ = v_isSharedCheck_6594_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6587_);
                            lean_inc(v_a_6586_);
                            lean_dec(v___x_6579_);
                            v___x_6589_ = lean_box(0);
                            v_isShared_6590_ = v_isSharedCheck_6594_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6570_);
                    lean_dec_ref(v___x_6565_);
                    v___x_6595_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6595_, 0, v_b_6569_);
                    lean_ctor_set(v___x_6595_, 1, v___y_6575_);
                    return v___x_6595_;
                }
            }
            1 => {
                if v_isShared_6590_ == 0 {
                    v___x_6592_ = v___x_6589_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6593_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6586_);
                    lean_ctor_set(v_reuseFailAlloc_6593_, 1, v_a_6587_);
                    v___x_6592_ = v_reuseFailAlloc_6593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(
    mut v___x_6596_: *mut LeanObject,
    mut v_as_6597_: *mut LeanObject,
    mut v_i_6598_: *mut LeanObject,
    mut v_stop_6599_: *mut LeanObject,
    mut v_b_6600_: *mut LeanObject,
    mut v___y_6601_: *mut LeanObject,
    mut v___y_6602_: *mut LeanObject,
    mut v___y_6603_: *mut LeanObject,
    mut v___y_6604_: *mut LeanObject,
    mut v___y_6605_: *mut LeanObject,
    mut v___y_6606_: *mut LeanObject,
    mut v___y_6607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6608_: usize = 0;
    let mut v_stop_boxed_6609_: usize = 0;
    let mut v_res_6610_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6608_ = lean_unbox_usize(v_i_6598_);
    lean_dec(v_i_6598_);
    v_stop_boxed_6609_ = lean_unbox_usize(v_stop_6599_);
    lean_dec(v_stop_6599_);
    v_res_6610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_6596_, v_as_6597_, v_i_boxed_6608_, v_stop_boxed_6609_, v_b_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_);
    lean_dec_ref(v___y_6605_);
    lean_dec(v___y_6604_);
    lean_dec(v___y_6603_);
    lean_dec(v___y_6602_);
    lean_dec_ref(v_as_6597_);
    return v_res_6610_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(
    mut v___x_6611_: *mut LeanObject,
    mut v_as_6612_: *mut LeanObject,
    mut v_i_6613_: usize,
    mut v_stop_6614_: usize,
    mut v_b_6615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: usize = 0;
    let mut v___x_6619_: usize = 0;
    let mut v___x_6621_: u8 = 0;
    let mut v_toConfigDecl_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: u8 = 0;
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6621_ = lean_usize_dec_eq(v_i_6613_, v_stop_6614_);
                if v___x_6621_ == 0 {
                    v_toConfigDecl_6622_ = lean_array_uget_borrowed(v_as_6612_, v_i_6613_);
                    v_name_6623_ = lean_ctor_get(v_toConfigDecl_6622_, 1);
                    v_kind_6624_ = lean_ctor_get(v_toConfigDecl_6622_, 2);
                    v_config_6625_ = lean_ctor_get(v_toConfigDecl_6622_, 3);
                    v___x_6626_ = l_Lake_ExternLib_keyword;
                    v___x_6627_ = lean_name_eq(v_kind_6624_, v___x_6626_);
                    if v___x_6627_ == 0 {
                        v___y_6617_ = v_b_6615_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_config_6625_);
                        lean_inc(v_name_6623_);
                        lean_inc_ref(v___x_6611_);
                        v___x_6628_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_6628_, 0, v___x_6611_);
                        lean_ctor_set(v___x_6628_, 1, v_name_6623_);
                        lean_ctor_set(v___x_6628_, 2, v_config_6625_);
                        v___x_6629_ = lean_array_push(v_b_6615_, v___x_6628_);
                        v___y_6617_ = v___x_6629_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_6611_);
                    return v_b_6615_;
                }
            }
            1 => {
                v___x_6618_ = 1usize;
                v___x_6619_ = lean_usize_add(v_i_6613_, v___x_6618_);
                v_i_6613_ = v___x_6619_;
                v_b_6615_ = v___y_6617_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(
    mut v___x_6630_: *mut LeanObject,
    mut v_as_6631_: *mut LeanObject,
    mut v_i_6632_: *mut LeanObject,
    mut v_stop_6633_: *mut LeanObject,
    mut v_b_6634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6635_: usize = 0;
    let mut v_stop_boxed_6636_: usize = 0;
    let mut v_res_6637_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6635_ = lean_unbox_usize(v_i_6632_);
    lean_dec(v_i_6632_);
    v_stop_boxed_6636_ = lean_unbox_usize(v_stop_6633_);
    lean_dec(v_stop_6633_);
    v_res_6637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_6630_, v_as_6631_, v_i_boxed_6635_, v_stop_boxed_6636_, v_b_6634_);
    lean_dec_ref(v_as_6631_);
    return v_res_6637_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(
    mut v_as_6638_: *mut LeanObject,
    mut v_i_6639_: usize,
    mut v_stop_6640_: usize,
    mut v_b_6641_: *mut LeanObject,
    mut v___y_6642_: *mut LeanObject,
    mut v___y_6643_: *mut LeanObject,
    mut v___y_6644_: *mut LeanObject,
    mut v___y_6645_: *mut LeanObject,
    mut v___y_6646_: *mut LeanObject,
    mut v___y_6647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6649_: u8 = 0;
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: u8 = 0;
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6657_: usize = 0;
    let mut v___x_6658_: usize = 0;
    let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: usize = 0;
    let mut v___x_6664_: usize = 0;
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6649_ = lean_usize_dec_eq(v_i_6639_, v_stop_6640_);
                if v___x_6649_ == 0 {
                    v___x_6650_ = lean_array_uget_borrowed(v_as_6638_, v_i_6639_);
                    v_lib_6651_ = lean_ctor_get(v___x_6650_, 0);
                    v_config_6652_ = lean_ctor_get(v_lib_6651_, 2);
                    v_nativeFacets_6653_ = lean_ctor_get(v_config_6652_, 8);
                    v___x_6654_ = 1;
                    v___x_6655_ = lean_box((v___x_6654_) as usize);
                    lean_inc_ref(v_nativeFacets_6653_);
                    v___x_6656_ = lean_apply_1(v_nativeFacets_6653_, v___x_6655_);
                    v_sz_6657_ = lean_array_size(v___x_6656_);
                    v___x_6658_ = 0usize;
                    lean_inc_ref(v___y_6642_);
                    lean_inc(v___x_6650_);
                    v___x_6659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_6650_, v_sz_6657_, v___x_6658_, v___x_6656_, v___y_6642_, v___y_6643_, v___y_6644_, v___y_6645_, v___y_6646_, v___y_6647_);
                    if lean_obj_tag(v___x_6659_) == 0 {
                        v_a_6660_ = lean_ctor_get(v___x_6659_, 0);
                        lean_inc(v_a_6660_);
                        v_a_6661_ = lean_ctor_get(v___x_6659_, 1);
                        lean_inc(v_a_6661_);
                        lean_dec_ref_known(v___x_6659_, 2);
                        v___x_6662_ = l_Array_append___redArg(v_b_6641_, v_a_6660_);
                        lean_dec(v_a_6660_);
                        v___x_6663_ = 1usize;
                        v___x_6664_ = lean_usize_add(v_i_6639_, v___x_6663_);
                        v_i_6639_ = v___x_6664_;
                        v_b_6641_ = v___x_6662_;
                        v___y_6647_ = v_a_6661_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_6642_);
                        lean_dec_ref(v_b_6641_);
                        return v___x_6659_;
                    }
                } else {
                    lean_dec_ref(v___y_6642_);
                    v___x_6666_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6666_, 0, v_b_6641_);
                    lean_ctor_set(v___x_6666_, 1, v___y_6647_);
                    return v___x_6666_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(
    mut v_as_6667_: *mut LeanObject,
    mut v_i_6668_: *mut LeanObject,
    mut v_stop_6669_: *mut LeanObject,
    mut v_b_6670_: *mut LeanObject,
    mut v___y_6671_: *mut LeanObject,
    mut v___y_6672_: *mut LeanObject,
    mut v___y_6673_: *mut LeanObject,
    mut v___y_6674_: *mut LeanObject,
    mut v___y_6675_: *mut LeanObject,
    mut v___y_6676_: *mut LeanObject,
    mut v___y_6677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6678_: usize = 0;
    let mut v_stop_boxed_6679_: usize = 0;
    let mut v_res_6680_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6678_ = lean_unbox_usize(v_i_6668_);
    lean_dec(v_i_6668_);
    v_stop_boxed_6679_ = lean_unbox_usize(v_stop_6669_);
    lean_dec(v_stop_6669_);
    v_res_6680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_6667_, v_i_boxed_6678_, v_stop_boxed_6679_, v_b_6670_, v___y_6671_, v___y_6672_, v___y_6673_, v___y_6674_, v___y_6675_, v___y_6676_);
    lean_dec_ref(v___y_6675_);
    lean_dec(v___y_6674_);
    lean_dec(v___y_6673_);
    lean_dec(v___y_6672_);
    lean_dec_ref(v_as_6667_);
    return v_res_6680_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(
    mut v___x_6681_: *mut LeanObject,
    mut v___x_6682_: *mut LeanObject,
    mut v_self_6683_: *mut LeanObject,
    mut v_dir_6684_: *mut LeanObject,
    mut v_targetDecls_6685_: *mut LeanObject,
    mut v_pkg_6686_: *mut LeanObject,
    mut v_name_6687_: *mut LeanObject,
    mut v_config_6688_: *mut LeanObject,
    mut v_config_6689_: *mut LeanObject,
    mut v___y_6690_: *mut LeanObject,
    mut v___y_6691_: *mut LeanObject,
    mut v___y_6692_: *mut LeanObject,
    mut v___y_6693_: *mut LeanObject,
    mut v___y_6694_: *mut LeanObject,
    mut v___y_6695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: u8 = 0;
    let mut v___x_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: u8 = 0;
    let mut v___x_6718_: u8 = 0;
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: u8 = 0;
    let mut v___x_6753_: u8 = 0;
    let mut v___x_6754_: usize = 0;
    let mut v___x_6755_: usize = 0;
    let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: usize = 0;
    let mut v___x_6758_: usize = 0;
    let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: u8 = 0;
    let mut v___x_6774_: u8 = 0;
    let mut v___x_6775_: usize = 0;
    let mut v___x_6776_: usize = 0;
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: usize = 0;
    let mut v___x_6779_: usize = 0;
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: u8 = 0;
    let mut v___x_6811_: u8 = 0;
    let mut v___x_6812_: usize = 0;
    let mut v___x_6813_: usize = 0;
    let mut v___x_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: usize = 0;
    let mut v___x_6816_: usize = 0;
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toArray_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6851_: u8 = 0;
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: u8 = 0;
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: u8 = 0;
    let mut v___x_6860_: usize = 0;
    let mut v___x_6861_: usize = 0;
    let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: usize = 0;
    let mut v___x_6864_: usize = 0;
    let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6867_: u8 = 0;
    let mut v_unused_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: u8 = 0;
    let mut v___x_6906_: u8 = 0;
    let mut v___x_6907_: usize = 0;
    let mut v___x_6908_: usize = 0;
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: usize = 0;
    let mut v___x_6911_: usize = 0;
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6930_: u8 = 0;
    let mut v___x_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6934_: u8 = 0;
    let mut v_a_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildDir_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: u8 = 0;
    let mut v___x_6954_: u8 = 0;
    let mut v___x_6955_: usize = 0;
    let mut v___x_6956_: usize = 0;
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: usize = 0;
    let mut v___x_6959_: usize = 0;
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6969_: u8 = 0;
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6973_: u8 = 0;
    let mut v___x_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: u8 = 0;
    let mut v___x_6978_: u8 = 0;
    let mut v___x_6979_: usize = 0;
    let mut v___x_6980_: usize = 0;
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: usize = 0;
    let mut v___x_6983_: usize = 0;
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6989_: u8 = 0;
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6993_: u8 = 0;
    let mut v_a_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6998_: u8 = 0;
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___y_6690_);
                lean_inc_ref(v___y_6694_);
                lean_inc(v___y_6693_);
                lean_inc(v___y_6692_);
                lean_inc(v___x_6682_);
                v___x_6885_ = lean_apply_7(
                    v___y_6690_,
                    v___x_6681_,
                    v___x_6682_,
                    v___y_6692_,
                    v___y_6693_,
                    v___y_6694_,
                    v___y_6695_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6885_) == 0 {
                    v_a_6886_ = lean_ctor_get(v___x_6885_, 0);
                    lean_inc(v_a_6886_);
                    v_a_6887_ = lean_ctor_get(v___x_6885_, 1);
                    lean_inc(v_a_6887_);
                    lean_dec_ref_known(v___x_6885_, 2);
                    v___x_6888_ = l_Lake_Job_await___redArg(v_a_6886_, v_a_6887_);
                    if lean_obj_tag(v___x_6888_) == 0 {
                        v_a_6889_ = lean_ctor_get(v___x_6888_, 0);
                        lean_inc(v_a_6889_);
                        v_a_6890_ = lean_ctor_get(v___x_6888_, 1);
                        lean_inc(v_a_6890_);
                        lean_dec_ref_known(v___x_6888_, 2);
                        v___x_6974_ = lean_unsigned_to_nat(0);
                        v___x_6975_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2;
                        v___x_6976_ = lean_array_get_size(v_a_6889_);
                        v___x_6977_ = lean_nat_dec_lt(v___x_6974_, v___x_6976_);
                        if v___x_6977_ == 0 {
                            v_a_6936_ = v___x_6975_;
                            v_a_6937_ = v_a_6890_;
                            state = 17;
                            continue;
                        } else {
                            v___x_6978_ = lean_nat_dec_le(v___x_6976_, v___x_6976_);
                            if v___x_6978_ == 0 {
                                if v___x_6977_ == 0 {
                                    v_a_6936_ = v___x_6975_;
                                    v_a_6937_ = v_a_6890_;
                                    state = 17;
                                    continue;
                                } else {
                                    v___x_6979_ = 0usize;
                                    v___x_6980_ = lean_usize_of_nat(v___x_6976_);
                                    lean_inc_ref(v___y_6690_);
                                    v___x_6981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_6889_, v___x_6979_, v___x_6980_, v___x_6975_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6890_);
                                    v___y_6962_ = v___x_6981_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                v___x_6982_ = 0usize;
                                v___x_6983_ = lean_usize_of_nat(v___x_6976_);
                                lean_inc_ref(v___y_6690_);
                                v___x_6984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_6889_, v___x_6982_, v___x_6983_, v___x_6975_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6890_);
                                v___y_6962_ = v___x_6984_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_6690_);
                        lean_dec_ref(v_config_6688_);
                        lean_dec(v_name_6687_);
                        lean_dec_ref(v_pkg_6686_);
                        lean_dec_ref(v_dir_6684_);
                        lean_dec_ref(v_self_6683_);
                        lean_dec(v___x_6682_);
                        v_a_6985_ = lean_ctor_get(v___x_6888_, 0);
                        v_a_6986_ = lean_ctor_get(v___x_6888_, 1);
                        v_isSharedCheck_6993_ = (!lean_is_exclusive(v___x_6888_)) as u8;
                        if v_isSharedCheck_6993_ == 0 {
                            v___x_6988_ = v___x_6888_;
                            v_isShared_6989_ = v_isSharedCheck_6993_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_6986_);
                            lean_inc(v_a_6985_);
                            lean_dec(v___x_6888_);
                            v___x_6988_ = lean_box(0);
                            v_isShared_6989_ = v_isSharedCheck_6993_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6690_);
                    lean_dec_ref(v_config_6688_);
                    lean_dec(v_name_6687_);
                    lean_dec_ref(v_pkg_6686_);
                    lean_dec_ref(v_dir_6684_);
                    lean_dec_ref(v_self_6683_);
                    lean_dec(v___x_6682_);
                    v_a_6994_ = lean_ctor_get(v___x_6885_, 0);
                    v_a_6995_ = lean_ctor_get(v___x_6885_, 1);
                    v_isSharedCheck_7002_ = (!lean_is_exclusive(v___x_6885_)) as u8;
                    if v_isSharedCheck_7002_ == 0 {
                        v___x_6997_ = v___x_6885_;
                        v_isShared_6998_ = v_isSharedCheck_7002_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_6995_);
                        lean_inc(v_a_6994_);
                        lean_dec(v___x_6885_);
                        v___x_6997_ = lean_box(0);
                        v_isShared_6998_ = v_isSharedCheck_7002_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_self_6683_);
                v___x_6707_ = l_Lake_LeanLib_libName(v_self_6683_);
                v___x_6708_ = l_System_FilePath_normalize(v___y_6701_);
                v___x_6709_ = l_Lake_joinRelative(v_dir_6684_, v___x_6708_);
                v___x_6710_ = l_System_FilePath_normalize(v___y_6699_);
                v___x_6711_ = l_Lake_joinRelative(v___x_6709_, v___x_6710_);
                v___x_6712_ = 0;
                v___x_6713_ = l_Lake_nameToSharedLib(v___x_6707_, v___x_6712_);
                v___x_6714_ = l_Lake_joinRelative(v___x_6711_, v___x_6713_);
                v___x_6715_ = l_Array_append___redArg(v___y_6700_, v___y_6703_);
                v___x_6716_ = l_Array_append___redArg(v___y_6698_, v___y_6702_);
                v___x_6717_ = l_Lake_LeanLib_isPlugin(v_self_6683_);
                v___x_6718_ = l_System_Platform_isWindows;
                v___x_6719_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once), _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
                v___x_6720_ = l_Lake_buildLeanSharedLib(
                    v___x_6707_,
                    v___x_6714_,
                    v___y_6704_,
                    v_a_6705_,
                    v___x_6715_,
                    v___x_6716_,
                    v___x_6717_,
                    v___x_6718_,
                    v___y_6690_,
                    v___x_6682_,
                    v___y_6692_,
                    v___y_6693_,
                    v___y_6694_,
                    v___x_6719_,
                );
                lean_dec(v___x_6682_);
                lean_dec_ref(v___y_6704_);
                v___x_6721_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6721_, 0, v___x_6720_);
                lean_ctor_set(v___x_6721_, 1, v_a_6706_);
                return v___x_6721_;
            }
            2 => {
                v___x_6725_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6725_, 0, v_a_6723_);
                lean_ctor_set(v___x_6725_, 1, v_a_6724_);
                return v___x_6725_;
            }
            3 => {
                if lean_obj_tag(v___y_6734_) == 0 {
                    v_a_6735_ = lean_ctor_get(v___y_6734_, 0);
                    lean_inc(v_a_6735_);
                    v_a_6736_ = lean_ctor_get(v___y_6734_, 1);
                    lean_inc(v_a_6736_);
                    lean_dec_ref_known(v___y_6734_, 2);
                    v___y_6698_ = v___y_6727_;
                    v___y_6699_ = v___y_6728_;
                    v___y_6700_ = v___y_6730_;
                    v___y_6701_ = v___y_6729_;
                    v___y_6702_ = v___y_6732_;
                    v___y_6703_ = v___y_6731_;
                    v___y_6704_ = v___y_6733_;
                    v_a_6705_ = v_a_6735_;
                    v_a_6706_ = v_a_6736_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___y_6733_);
                    lean_dec_ref(v___y_6730_);
                    lean_dec_ref(v___y_6729_);
                    lean_dec_ref(v___y_6728_);
                    lean_dec_ref(v___y_6727_);
                    lean_dec_ref(v___y_6690_);
                    lean_dec_ref(v_dir_6684_);
                    lean_dec_ref(v_self_6683_);
                    lean_dec(v___x_6682_);
                    v_a_6737_ = lean_ctor_get(v___y_6734_, 0);
                    lean_inc(v_a_6737_);
                    v_a_6738_ = lean_ctor_get(v___y_6734_, 1);
                    lean_inc(v_a_6738_);
                    lean_dec_ref_known(v___y_6734_, 2);
                    v_a_6723_ = v_a_6737_;
                    v_a_6724_ = v_a_6738_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_6751_ = lean_array_get_size(v___y_6750_);
                v___x_6752_ = lean_nat_dec_lt(v___y_6748_, v___x_6751_);
                if v___x_6752_ == 0 {
                    lean_dec_ref(v___y_6750_);
                    v___y_6698_ = v___y_6740_;
                    v___y_6699_ = v___y_6741_;
                    v___y_6700_ = v___y_6743_;
                    v___y_6701_ = v___y_6742_;
                    v___y_6702_ = v___y_6747_;
                    v___y_6703_ = v___y_6746_;
                    v___y_6704_ = v___y_6749_;
                    v_a_6705_ = v___y_6745_;
                    v_a_6706_ = v___y_6744_;
                    state = 1;
                    continue;
                } else {
                    v___x_6753_ = lean_nat_dec_le(v___x_6751_, v___x_6751_);
                    if v___x_6753_ == 0 {
                        if v___x_6752_ == 0 {
                            lean_dec_ref(v___y_6750_);
                            v___y_6698_ = v___y_6740_;
                            v___y_6699_ = v___y_6741_;
                            v___y_6700_ = v___y_6743_;
                            v___y_6701_ = v___y_6742_;
                            v___y_6702_ = v___y_6747_;
                            v___y_6703_ = v___y_6746_;
                            v___y_6704_ = v___y_6749_;
                            v_a_6705_ = v___y_6745_;
                            v_a_6706_ = v___y_6744_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6754_ = 0usize;
                            v___x_6755_ = lean_usize_of_nat(v___x_6751_);
                            lean_inc_ref(v___y_6690_);
                            v___x_6756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_6750_, v___x_6754_, v___x_6755_, v___y_6745_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6744_);
                            lean_dec_ref(v___y_6750_);
                            v___y_6727_ = v___y_6740_;
                            v___y_6728_ = v___y_6741_;
                            v___y_6729_ = v___y_6742_;
                            v___y_6730_ = v___y_6743_;
                            v___y_6731_ = v___y_6746_;
                            v___y_6732_ = v___y_6747_;
                            v___y_6733_ = v___y_6749_;
                            v___y_6734_ = v___x_6756_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_6757_ = 0usize;
                        v___x_6758_ = lean_usize_of_nat(v___x_6751_);
                        lean_inc_ref(v___y_6690_);
                        v___x_6759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_6750_, v___x_6757_, v___x_6758_, v___y_6745_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6744_);
                        lean_dec_ref(v___y_6750_);
                        v___y_6727_ = v___y_6740_;
                        v___y_6728_ = v___y_6741_;
                        v___y_6729_ = v___y_6742_;
                        v___y_6730_ = v___y_6743_;
                        v___y_6731_ = v___y_6746_;
                        v___y_6732_ = v___y_6747_;
                        v___y_6733_ = v___y_6749_;
                        v___y_6734_ = v___x_6759_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6771_ = lean_mk_empty_array_with_capacity(v___y_6767_);
                v___x_6772_ = lean_array_get_size(v_targetDecls_6685_);
                v___x_6773_ = lean_nat_dec_lt(v___y_6767_, v___x_6772_);
                if v___x_6773_ == 0 {
                    lean_dec_ref(v_pkg_6686_);
                    v___y_6740_ = v___y_6761_;
                    v___y_6741_ = v___y_6762_;
                    v___y_6742_ = v___y_6764_;
                    v___y_6743_ = v___y_6763_;
                    v___y_6744_ = v_a_6770_;
                    v___y_6745_ = v_a_6769_;
                    v___y_6746_ = v___y_6766_;
                    v___y_6747_ = v___y_6765_;
                    v___y_6748_ = v___y_6767_;
                    v___y_6749_ = v___y_6768_;
                    v___y_6750_ = v___x_6771_;
                    state = 4;
                    continue;
                } else {
                    v___x_6774_ = lean_nat_dec_le(v___x_6772_, v___x_6772_);
                    if v___x_6774_ == 0 {
                        if v___x_6773_ == 0 {
                            lean_dec_ref(v_pkg_6686_);
                            v___y_6740_ = v___y_6761_;
                            v___y_6741_ = v___y_6762_;
                            v___y_6742_ = v___y_6764_;
                            v___y_6743_ = v___y_6763_;
                            v___y_6744_ = v_a_6770_;
                            v___y_6745_ = v_a_6769_;
                            v___y_6746_ = v___y_6766_;
                            v___y_6747_ = v___y_6765_;
                            v___y_6748_ = v___y_6767_;
                            v___y_6749_ = v___y_6768_;
                            v___y_6750_ = v___x_6771_;
                            state = 4;
                            continue;
                        } else {
                            v___x_6775_ = 0usize;
                            v___x_6776_ = lean_usize_of_nat(v___x_6772_);
                            v___x_6777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_6686_, v_targetDecls_6685_, v___x_6775_, v___x_6776_, v___x_6771_);
                            v___y_6740_ = v___y_6761_;
                            v___y_6741_ = v___y_6762_;
                            v___y_6742_ = v___y_6764_;
                            v___y_6743_ = v___y_6763_;
                            v___y_6744_ = v_a_6770_;
                            v___y_6745_ = v_a_6769_;
                            v___y_6746_ = v___y_6766_;
                            v___y_6747_ = v___y_6765_;
                            v___y_6748_ = v___y_6767_;
                            v___y_6749_ = v___y_6768_;
                            v___y_6750_ = v___x_6777_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_6778_ = 0usize;
                        v___x_6779_ = lean_usize_of_nat(v___x_6772_);
                        v___x_6780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_6686_, v_targetDecls_6685_, v___x_6778_, v___x_6779_, v___x_6771_);
                        v___y_6740_ = v___y_6761_;
                        v___y_6741_ = v___y_6762_;
                        v___y_6742_ = v___y_6764_;
                        v___y_6743_ = v___y_6763_;
                        v___y_6744_ = v_a_6770_;
                        v___y_6745_ = v_a_6769_;
                        v___y_6746_ = v___y_6766_;
                        v___y_6747_ = v___y_6765_;
                        v___y_6748_ = v___y_6767_;
                        v___y_6749_ = v___y_6768_;
                        v___y_6750_ = v___x_6780_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                if lean_obj_tag(v___y_6790_) == 0 {
                    v_a_6791_ = lean_ctor_get(v___y_6790_, 0);
                    lean_inc(v_a_6791_);
                    v_a_6792_ = lean_ctor_get(v___y_6790_, 1);
                    lean_inc(v_a_6792_);
                    lean_dec_ref_known(v___y_6790_, 2);
                    v___y_6761_ = v___y_6782_;
                    v___y_6762_ = v___y_6783_;
                    v___y_6763_ = v___y_6785_;
                    v___y_6764_ = v___y_6784_;
                    v___y_6765_ = v___y_6787_;
                    v___y_6766_ = v___y_6786_;
                    v___y_6767_ = v___y_6788_;
                    v___y_6768_ = v___y_6789_;
                    v_a_6769_ = v_a_6791_;
                    v_a_6770_ = v_a_6792_;
                    state = 5;
                    continue;
                } else {
                    lean_dec_ref(v___y_6789_);
                    lean_dec_ref(v___y_6785_);
                    lean_dec_ref(v___y_6784_);
                    lean_dec_ref(v___y_6783_);
                    lean_dec_ref(v___y_6782_);
                    lean_dec_ref(v___y_6690_);
                    lean_dec_ref(v_pkg_6686_);
                    lean_dec_ref(v_dir_6684_);
                    lean_dec_ref(v_self_6683_);
                    lean_dec(v___x_6682_);
                    v_a_6793_ = lean_ctor_get(v___y_6790_, 0);
                    lean_inc(v_a_6793_);
                    v_a_6794_ = lean_ctor_get(v___y_6790_, 1);
                    lean_inc(v_a_6794_);
                    lean_dec_ref_known(v___y_6790_, 2);
                    v_a_6723_ = v_a_6793_;
                    v_a_6724_ = v_a_6794_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v___x_6808_ = l_Array_append___redArg(v___y_6803_, v___y_6800_);
                v___x_6809_ = lean_array_get_size(v___x_6808_);
                v___x_6810_ = lean_nat_dec_lt(v___y_6804_, v___x_6809_);
                if v___x_6810_ == 0 {
                    lean_dec_ref(v___x_6808_);
                    v___y_6761_ = v___y_6796_;
                    v___y_6762_ = v___y_6797_;
                    v___y_6763_ = v___y_6799_;
                    v___y_6764_ = v___y_6798_;
                    v___y_6765_ = v___y_6802_;
                    v___y_6766_ = v___y_6801_;
                    v___y_6767_ = v___y_6804_;
                    v___y_6768_ = v___y_6805_;
                    v_a_6769_ = v_snd_6806_;
                    v_a_6770_ = v_a_6807_;
                    state = 5;
                    continue;
                } else {
                    v___x_6811_ = lean_nat_dec_le(v___x_6809_, v___x_6809_);
                    if v___x_6811_ == 0 {
                        if v___x_6810_ == 0 {
                            lean_dec_ref(v___x_6808_);
                            v___y_6761_ = v___y_6796_;
                            v___y_6762_ = v___y_6797_;
                            v___y_6763_ = v___y_6799_;
                            v___y_6764_ = v___y_6798_;
                            v___y_6765_ = v___y_6802_;
                            v___y_6766_ = v___y_6801_;
                            v___y_6767_ = v___y_6804_;
                            v___y_6768_ = v___y_6805_;
                            v_a_6769_ = v_snd_6806_;
                            v_a_6770_ = v_a_6807_;
                            state = 5;
                            continue;
                        } else {
                            v___x_6812_ = 0usize;
                            v___x_6813_ = lean_usize_of_nat(v___x_6809_);
                            lean_inc_ref(v___y_6690_);
                            lean_inc_ref(v_pkg_6686_);
                            v___x_6814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_6686_, v___x_6808_, v___x_6812_, v___x_6813_, v_snd_6806_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6807_);
                            lean_dec_ref(v___x_6808_);
                            v___y_6782_ = v___y_6796_;
                            v___y_6783_ = v___y_6797_;
                            v___y_6784_ = v___y_6798_;
                            v___y_6785_ = v___y_6799_;
                            v___y_6786_ = v___y_6801_;
                            v___y_6787_ = v___y_6802_;
                            v___y_6788_ = v___y_6804_;
                            v___y_6789_ = v___y_6805_;
                            v___y_6790_ = v___x_6814_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_6815_ = 0usize;
                        v___x_6816_ = lean_usize_of_nat(v___x_6809_);
                        lean_inc_ref(v___y_6690_);
                        lean_inc_ref(v_pkg_6686_);
                        v___x_6817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_6686_, v___x_6808_, v___x_6815_, v___x_6816_, v_snd_6806_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6807_);
                        lean_dec_ref(v___x_6808_);
                        v___y_6782_ = v___y_6796_;
                        v___y_6783_ = v___y_6797_;
                        v___y_6784_ = v___y_6798_;
                        v___y_6785_ = v___y_6799_;
                        v___y_6786_ = v___y_6801_;
                        v___y_6787_ = v___y_6802_;
                        v___y_6788_ = v___y_6804_;
                        v___y_6789_ = v___y_6805_;
                        v___y_6790_ = v___x_6817_;
                        state = 6;
                        continue;
                    }
                }
            }
            8 => {
                if lean_obj_tag(v___y_6829_) == 0 {
                    v_a_6830_ = lean_ctor_get(v___y_6829_, 0);
                    lean_inc(v_a_6830_);
                    v_a_6831_ = lean_ctor_get(v___y_6829_, 1);
                    lean_inc(v_a_6831_);
                    lean_dec_ref_known(v___y_6829_, 2);
                    v_snd_6832_ = lean_ctor_get(v_a_6830_, 1);
                    lean_inc(v_snd_6832_);
                    lean_dec(v_a_6830_);
                    v___y_6796_ = v___y_6819_;
                    v___y_6797_ = v___y_6820_;
                    v___y_6798_ = v___y_6822_;
                    v___y_6799_ = v___y_6821_;
                    v___y_6800_ = v___y_6823_;
                    v___y_6801_ = v___y_6826_;
                    v___y_6802_ = v___y_6825_;
                    v___y_6803_ = v___y_6824_;
                    v___y_6804_ = v___y_6827_;
                    v___y_6805_ = v___y_6828_;
                    v_snd_6806_ = v_snd_6832_;
                    v_a_6807_ = v_a_6831_;
                    state = 7;
                    continue;
                } else {
                    lean_dec_ref(v___y_6828_);
                    lean_dec_ref(v___y_6824_);
                    lean_dec_ref(v___y_6822_);
                    lean_dec_ref(v___y_6821_);
                    lean_dec_ref(v___y_6820_);
                    lean_dec_ref(v___y_6819_);
                    lean_dec_ref(v___y_6690_);
                    lean_dec_ref(v_pkg_6686_);
                    lean_dec_ref(v_dir_6684_);
                    lean_dec_ref(v_self_6683_);
                    lean_dec(v___x_6682_);
                    v_a_6833_ = lean_ctor_get(v___y_6829_, 0);
                    lean_inc(v_a_6833_);
                    v_a_6834_ = lean_ctor_get(v___y_6829_, 1);
                    lean_inc(v_a_6834_);
                    lean_dec_ref_known(v___y_6829_, 2);
                    v_a_6723_ = v_a_6833_;
                    v_a_6724_ = v_a_6834_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_toArray_6848_ = lean_ctor_get(v_a_6846_, 1);
                v_isSharedCheck_6867_ = (!lean_is_exclusive(v_a_6846_)) as u8;
                if v_isSharedCheck_6867_ == 0 {
                    v_unused_6868_ = lean_ctor_get(v_a_6846_, 0);
                    lean_dec(v_unused_6868_);
                    v___x_6850_ = v_a_6846_;
                    v_isShared_6851_ = v_isSharedCheck_6867_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_toArray_6848_);
                    lean_dec(v_a_6846_);
                    v___x_6850_ = lean_box(0);
                    v_isShared_6851_ = v_isSharedCheck_6867_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_6852_ = lean_mk_empty_array_with_capacity(v___y_6844_);
                v___x_6853_ = lean_array_get_size(v_toArray_6848_);
                v___x_6854_ = lean_nat_dec_lt(v___y_6844_, v___x_6853_);
                if v___x_6854_ == 0 {
                    lean_del_object(v___x_6850_);
                    lean_dec_ref(v_toArray_6848_);
                    lean_dec(v_name_6687_);
                    v___y_6796_ = v___y_6836_;
                    v___y_6797_ = v___y_6837_;
                    v___y_6798_ = v___y_6839_;
                    v___y_6799_ = v___y_6838_;
                    v___y_6800_ = v___y_6840_;
                    v___y_6801_ = v___y_6843_;
                    v___y_6802_ = v___y_6842_;
                    v___y_6803_ = v___y_6841_;
                    v___y_6804_ = v___y_6844_;
                    v___y_6805_ = v___y_6845_;
                    v_snd_6806_ = v___x_6852_;
                    v_a_6807_ = v_a_6847_;
                    state = 7;
                    continue;
                } else {
                    v___x_6855_ = l_Lean_NameSet_empty;
                    v___x_6856_ = l_Lean_NameSet_insert(v___x_6855_, v_name_6687_);
                    lean_inc_ref(v___x_6852_);
                    if v_isShared_6851_ == 0 {
                        lean_ctor_set(v___x_6850_, 1, v___x_6852_);
                        lean_ctor_set(v___x_6850_, 0, v___x_6856_);
                        v___x_6858_ = v___x_6850_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6866_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6866_, 0, v___x_6856_);
                        lean_ctor_set(v_reuseFailAlloc_6866_, 1, v___x_6852_);
                        v___x_6858_ = v_reuseFailAlloc_6866_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                v___x_6859_ = lean_nat_dec_le(v___x_6853_, v___x_6853_);
                if v___x_6859_ == 0 {
                    if v___x_6854_ == 0 {
                        lean_dec_ref(v___x_6858_);
                        lean_dec_ref(v_toArray_6848_);
                        v___y_6796_ = v___y_6836_;
                        v___y_6797_ = v___y_6837_;
                        v___y_6798_ = v___y_6839_;
                        v___y_6799_ = v___y_6838_;
                        v___y_6800_ = v___y_6840_;
                        v___y_6801_ = v___y_6843_;
                        v___y_6802_ = v___y_6842_;
                        v___y_6803_ = v___y_6841_;
                        v___y_6804_ = v___y_6844_;
                        v___y_6805_ = v___y_6845_;
                        v_snd_6806_ = v___x_6852_;
                        v_a_6807_ = v_a_6847_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec_ref(v___x_6852_);
                        v___x_6860_ = 0usize;
                        v___x_6861_ = lean_usize_of_nat(v___x_6853_);
                        lean_inc_ref(v___y_6690_);
                        v___x_6862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_6848_, v___x_6860_, v___x_6861_, v___x_6858_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6847_);
                        lean_dec_ref(v_toArray_6848_);
                        v___y_6819_ = v___y_6836_;
                        v___y_6820_ = v___y_6837_;
                        v___y_6821_ = v___y_6838_;
                        v___y_6822_ = v___y_6839_;
                        v___y_6823_ = v___y_6840_;
                        v___y_6824_ = v___y_6841_;
                        v___y_6825_ = v___y_6842_;
                        v___y_6826_ = v___y_6843_;
                        v___y_6827_ = v___y_6844_;
                        v___y_6828_ = v___y_6845_;
                        v___y_6829_ = v___x_6862_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_6852_);
                    v___x_6863_ = 0usize;
                    v___x_6864_ = lean_usize_of_nat(v___x_6853_);
                    lean_inc_ref(v___y_6690_);
                    v___x_6865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_6848_, v___x_6863_, v___x_6864_, v___x_6858_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6847_);
                    lean_dec_ref(v_toArray_6848_);
                    v___y_6819_ = v___y_6836_;
                    v___y_6820_ = v___y_6837_;
                    v___y_6821_ = v___y_6838_;
                    v___y_6822_ = v___y_6839_;
                    v___y_6823_ = v___y_6840_;
                    v___y_6824_ = v___y_6841_;
                    v___y_6825_ = v___y_6842_;
                    v___y_6826_ = v___y_6843_;
                    v___y_6827_ = v___y_6844_;
                    v___y_6828_ = v___y_6845_;
                    v___y_6829_ = v___x_6865_;
                    state = 8;
                    continue;
                }
            }
            12 => {
                if lean_obj_tag(v___y_6880_) == 0 {
                    v_a_6881_ = lean_ctor_get(v___y_6880_, 0);
                    lean_inc(v_a_6881_);
                    v_a_6882_ = lean_ctor_get(v___y_6880_, 1);
                    lean_inc(v_a_6882_);
                    lean_dec_ref_known(v___y_6880_, 2);
                    v___y_6836_ = v___y_6870_;
                    v___y_6837_ = v___y_6871_;
                    v___y_6838_ = v___y_6873_;
                    v___y_6839_ = v___y_6872_;
                    v___y_6840_ = v___y_6874_;
                    v___y_6841_ = v___y_6877_;
                    v___y_6842_ = v___y_6876_;
                    v___y_6843_ = v___y_6875_;
                    v___y_6844_ = v___y_6878_;
                    v___y_6845_ = v___y_6879_;
                    v_a_6846_ = v_a_6881_;
                    v_a_6847_ = v_a_6882_;
                    state = 9;
                    continue;
                } else {
                    lean_dec_ref(v___y_6879_);
                    lean_dec_ref(v___y_6877_);
                    lean_dec_ref(v___y_6873_);
                    lean_dec_ref(v___y_6872_);
                    lean_dec_ref(v___y_6871_);
                    lean_dec_ref(v___y_6870_);
                    lean_dec_ref(v___y_6690_);
                    lean_dec(v_name_6687_);
                    lean_dec_ref(v_pkg_6686_);
                    lean_dec_ref(v_dir_6684_);
                    lean_dec_ref(v_self_6683_);
                    lean_dec(v___x_6682_);
                    v_a_6883_ = lean_ctor_get(v___y_6880_, 0);
                    lean_inc(v_a_6883_);
                    v_a_6884_ = lean_ctor_get(v___y_6880_, 1);
                    lean_inc(v_a_6884_);
                    lean_dec_ref_known(v___y_6880_, 2);
                    v_a_6723_ = v_a_6883_;
                    v_a_6724_ = v_a_6884_;
                    state = 2;
                    continue;
                }
            }
            13 => {
                v___x_6903_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
                v___x_6904_ = lean_array_get_size(v_a_6889_);
                v___x_6905_ = lean_nat_dec_lt(v___y_6900_, v___x_6904_);
                if v___x_6905_ == 0 {
                    lean_dec(v_a_6889_);
                    v___y_6836_ = v___y_6892_;
                    v___y_6837_ = v___y_6893_;
                    v___y_6838_ = v___y_6894_;
                    v___y_6839_ = v___y_6895_;
                    v___y_6840_ = v___y_6896_;
                    v___y_6841_ = v___y_6897_;
                    v___y_6842_ = v___y_6898_;
                    v___y_6843_ = v___y_6899_;
                    v___y_6844_ = v___y_6900_;
                    v___y_6845_ = v_a_6901_;
                    v_a_6846_ = v___x_6903_;
                    v_a_6847_ = v_a_6902_;
                    state = 9;
                    continue;
                } else {
                    v___x_6906_ = lean_nat_dec_le(v___x_6904_, v___x_6904_);
                    if v___x_6906_ == 0 {
                        if v___x_6905_ == 0 {
                            lean_dec(v_a_6889_);
                            v___y_6836_ = v___y_6892_;
                            v___y_6837_ = v___y_6893_;
                            v___y_6838_ = v___y_6894_;
                            v___y_6839_ = v___y_6895_;
                            v___y_6840_ = v___y_6896_;
                            v___y_6841_ = v___y_6897_;
                            v___y_6842_ = v___y_6898_;
                            v___y_6843_ = v___y_6899_;
                            v___y_6844_ = v___y_6900_;
                            v___y_6845_ = v_a_6901_;
                            v_a_6846_ = v___x_6903_;
                            v_a_6847_ = v_a_6902_;
                            state = 9;
                            continue;
                        } else {
                            v___x_6907_ = 0usize;
                            v___x_6908_ = lean_usize_of_nat(v___x_6904_);
                            lean_inc_ref(v___y_6690_);
                            v___x_6909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_6889_, v___x_6907_, v___x_6908_, v___x_6903_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6902_);
                            lean_dec(v_a_6889_);
                            v___y_6870_ = v___y_6892_;
                            v___y_6871_ = v___y_6893_;
                            v___y_6872_ = v___y_6895_;
                            v___y_6873_ = v___y_6894_;
                            v___y_6874_ = v___y_6896_;
                            v___y_6875_ = v___y_6899_;
                            v___y_6876_ = v___y_6898_;
                            v___y_6877_ = v___y_6897_;
                            v___y_6878_ = v___y_6900_;
                            v___y_6879_ = v_a_6901_;
                            v___y_6880_ = v___x_6909_;
                            state = 12;
                            continue;
                        }
                    } else {
                        v___x_6910_ = 0usize;
                        v___x_6911_ = lean_usize_of_nat(v___x_6904_);
                        lean_inc_ref(v___y_6690_);
                        v___x_6912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_6889_, v___x_6910_, v___x_6911_, v___x_6903_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6902_);
                        lean_dec(v_a_6889_);
                        v___y_6870_ = v___y_6892_;
                        v___y_6871_ = v___y_6893_;
                        v___y_6872_ = v___y_6895_;
                        v___y_6873_ = v___y_6894_;
                        v___y_6874_ = v___y_6896_;
                        v___y_6875_ = v___y_6899_;
                        v___y_6876_ = v___y_6898_;
                        v___y_6877_ = v___y_6897_;
                        v___y_6878_ = v___y_6900_;
                        v___y_6879_ = v_a_6901_;
                        v___y_6880_ = v___x_6912_;
                        state = 12;
                        continue;
                    }
                }
            }
            14 => {
                if lean_obj_tag(v___y_6923_) == 0 {
                    v_a_6924_ = lean_ctor_get(v___y_6923_, 0);
                    lean_inc(v_a_6924_);
                    v_a_6925_ = lean_ctor_get(v___y_6923_, 1);
                    lean_inc(v_a_6925_);
                    lean_dec_ref_known(v___y_6923_, 2);
                    v___y_6892_ = v___y_6914_;
                    v___y_6893_ = v___y_6915_;
                    v___y_6894_ = v___y_6917_;
                    v___y_6895_ = v___y_6916_;
                    v___y_6896_ = v___y_6918_;
                    v___y_6897_ = v___y_6921_;
                    v___y_6898_ = v___y_6920_;
                    v___y_6899_ = v___y_6919_;
                    v___y_6900_ = v___y_6922_;
                    v_a_6901_ = v_a_6924_;
                    v_a_6902_ = v_a_6925_;
                    state = 13;
                    continue;
                } else {
                    lean_dec_ref(v___y_6921_);
                    lean_dec_ref(v___y_6917_);
                    lean_dec_ref(v___y_6916_);
                    lean_dec_ref(v___y_6915_);
                    lean_dec_ref(v___y_6914_);
                    lean_dec(v_a_6889_);
                    lean_dec_ref(v___y_6690_);
                    lean_dec(v_name_6687_);
                    lean_dec_ref(v_pkg_6686_);
                    lean_dec_ref(v_dir_6684_);
                    lean_dec_ref(v_self_6683_);
                    lean_dec(v___x_6682_);
                    v_a_6926_ = lean_ctor_get(v___y_6923_, 0);
                    v_a_6927_ = lean_ctor_get(v___y_6923_, 1);
                    v_isSharedCheck_6934_ = (!lean_is_exclusive(v___y_6923_)) as u8;
                    if v_isSharedCheck_6934_ == 0 {
                        v___x_6929_ = v___y_6923_;
                        v_isShared_6930_ = v_isSharedCheck_6934_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_6927_);
                        lean_inc(v_a_6926_);
                        lean_dec(v___y_6923_);
                        v___x_6929_ = lean_box(0);
                        v_isShared_6930_ = v_isSharedCheck_6934_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_6930_ == 0 {
                    v___x_6932_ = v___x_6929_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6933_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6933_, 0, v_a_6926_);
                    lean_ctor_set(v_reuseFailAlloc_6933_, 1, v_a_6927_);
                    v___x_6932_ = v_reuseFailAlloc_6933_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6932_;
            }
            17 => {
                v_toLeanConfig_6938_ = lean_ctor_get(v_config_6688_, 1);
                lean_inc_ref(v_toLeanConfig_6938_);
                v_toLeanConfig_6939_ = lean_ctor_get(v_config_6689_, 0);
                v_buildDir_6940_ = lean_ctor_get(v_config_6688_, 5);
                lean_inc_ref(v_buildDir_6940_);
                v_nativeLibDir_6941_ = lean_ctor_get(v_config_6688_, 7);
                lean_inc_ref(v_nativeLibDir_6941_);
                lean_dec_ref(v_config_6688_);
                v_moreLinkObjs_6942_ = lean_ctor_get(v_toLeanConfig_6938_, 6);
                lean_inc_ref(v_moreLinkObjs_6942_);
                v_moreLinkLibs_6943_ = lean_ctor_get(v_toLeanConfig_6938_, 7);
                lean_inc_ref(v_moreLinkLibs_6943_);
                v_moreLinkArgs_6944_ = lean_ctor_get(v_toLeanConfig_6938_, 8);
                lean_inc_ref(v_moreLinkArgs_6944_);
                v_weakLinkArgs_6945_ = lean_ctor_get(v_toLeanConfig_6938_, 9);
                lean_inc_ref(v_weakLinkArgs_6945_);
                lean_dec_ref(v_toLeanConfig_6938_);
                v_moreLinkObjs_6946_ = lean_ctor_get(v_toLeanConfig_6939_, 6);
                v_moreLinkLibs_6947_ = lean_ctor_get(v_toLeanConfig_6939_, 7);
                v_moreLinkArgs_6948_ = lean_ctor_get(v_toLeanConfig_6939_, 8);
                v_weakLinkArgs_6949_ = lean_ctor_get(v_toLeanConfig_6939_, 9);
                v___x_6950_ = l_Array_append___redArg(v_moreLinkObjs_6942_, v_moreLinkObjs_6946_);
                v___x_6951_ = lean_unsigned_to_nat(0);
                v___x_6952_ = lean_array_get_size(v___x_6950_);
                v___x_6953_ = lean_nat_dec_lt(v___x_6951_, v___x_6952_);
                if v___x_6953_ == 0 {
                    lean_dec_ref(v___x_6950_);
                    v___y_6892_ = v_moreLinkArgs_6944_;
                    v___y_6893_ = v_nativeLibDir_6941_;
                    v___y_6894_ = v_weakLinkArgs_6945_;
                    v___y_6895_ = v_buildDir_6940_;
                    v___y_6896_ = v_moreLinkLibs_6947_;
                    v___y_6897_ = v_moreLinkLibs_6943_;
                    v___y_6898_ = v_moreLinkArgs_6948_;
                    v___y_6899_ = v_weakLinkArgs_6949_;
                    v___y_6900_ = v___x_6951_;
                    v_a_6901_ = v_a_6936_;
                    v_a_6902_ = v_a_6937_;
                    state = 13;
                    continue;
                } else {
                    v___x_6954_ = lean_nat_dec_le(v___x_6952_, v___x_6952_);
                    if v___x_6954_ == 0 {
                        if v___x_6953_ == 0 {
                            lean_dec_ref(v___x_6950_);
                            v___y_6892_ = v_moreLinkArgs_6944_;
                            v___y_6893_ = v_nativeLibDir_6941_;
                            v___y_6894_ = v_weakLinkArgs_6945_;
                            v___y_6895_ = v_buildDir_6940_;
                            v___y_6896_ = v_moreLinkLibs_6947_;
                            v___y_6897_ = v_moreLinkLibs_6943_;
                            v___y_6898_ = v_moreLinkArgs_6948_;
                            v___y_6899_ = v_weakLinkArgs_6949_;
                            v___y_6900_ = v___x_6951_;
                            v_a_6901_ = v_a_6936_;
                            v_a_6902_ = v_a_6937_;
                            state = 13;
                            continue;
                        } else {
                            v___x_6955_ = 0usize;
                            v___x_6956_ = lean_usize_of_nat(v___x_6952_);
                            lean_inc_ref(v___y_6690_);
                            lean_inc_ref(v_pkg_6686_);
                            v___x_6957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_6686_, v___x_6950_, v___x_6955_, v___x_6956_, v_a_6936_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6937_);
                            lean_dec_ref(v___x_6950_);
                            v___y_6914_ = v_moreLinkArgs_6944_;
                            v___y_6915_ = v_nativeLibDir_6941_;
                            v___y_6916_ = v_buildDir_6940_;
                            v___y_6917_ = v_weakLinkArgs_6945_;
                            v___y_6918_ = v_moreLinkLibs_6947_;
                            v___y_6919_ = v_weakLinkArgs_6949_;
                            v___y_6920_ = v_moreLinkArgs_6948_;
                            v___y_6921_ = v_moreLinkLibs_6943_;
                            v___y_6922_ = v___x_6951_;
                            v___y_6923_ = v___x_6957_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___x_6958_ = 0usize;
                        v___x_6959_ = lean_usize_of_nat(v___x_6952_);
                        lean_inc_ref(v___y_6690_);
                        lean_inc_ref(v_pkg_6686_);
                        v___x_6960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_6686_, v___x_6950_, v___x_6958_, v___x_6959_, v_a_6936_, v___y_6690_, v___x_6682_, v___y_6692_, v___y_6693_, v___y_6694_, v_a_6937_);
                        lean_dec_ref(v___x_6950_);
                        v___y_6914_ = v_moreLinkArgs_6944_;
                        v___y_6915_ = v_nativeLibDir_6941_;
                        v___y_6916_ = v_buildDir_6940_;
                        v___y_6917_ = v_weakLinkArgs_6945_;
                        v___y_6918_ = v_moreLinkLibs_6947_;
                        v___y_6919_ = v_weakLinkArgs_6949_;
                        v___y_6920_ = v_moreLinkArgs_6948_;
                        v___y_6921_ = v_moreLinkLibs_6943_;
                        v___y_6922_ = v___x_6951_;
                        v___y_6923_ = v___x_6960_;
                        state = 14;
                        continue;
                    }
                }
            }
            18 => {
                if lean_obj_tag(v___y_6962_) == 0 {
                    v_a_6963_ = lean_ctor_get(v___y_6962_, 0);
                    lean_inc(v_a_6963_);
                    v_a_6964_ = lean_ctor_get(v___y_6962_, 1);
                    lean_inc(v_a_6964_);
                    lean_dec_ref_known(v___y_6962_, 2);
                    v_a_6936_ = v_a_6963_;
                    v_a_6937_ = v_a_6964_;
                    state = 17;
                    continue;
                } else {
                    lean_dec(v_a_6889_);
                    lean_dec_ref(v___y_6690_);
                    lean_dec_ref(v_config_6688_);
                    lean_dec(v_name_6687_);
                    lean_dec_ref(v_pkg_6686_);
                    lean_dec_ref(v_dir_6684_);
                    lean_dec_ref(v_self_6683_);
                    lean_dec(v___x_6682_);
                    v_a_6965_ = lean_ctor_get(v___y_6962_, 0);
                    v_a_6966_ = lean_ctor_get(v___y_6962_, 1);
                    v_isSharedCheck_6973_ = (!lean_is_exclusive(v___y_6962_)) as u8;
                    if v_isSharedCheck_6973_ == 0 {
                        v___x_6968_ = v___y_6962_;
                        v_isShared_6969_ = v_isSharedCheck_6973_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_6966_);
                        lean_inc(v_a_6965_);
                        lean_dec(v___y_6962_);
                        v___x_6968_ = lean_box(0);
                        v_isShared_6969_ = v_isSharedCheck_6973_;
                        state = 19;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_6969_ == 0 {
                    v___x_6971_ = v___x_6968_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6972_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6972_, 0, v_a_6965_);
                    lean_ctor_set(v_reuseFailAlloc_6972_, 1, v_a_6966_);
                    v___x_6971_ = v_reuseFailAlloc_6972_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6971_;
            }
            21 => {
                if v_isShared_6989_ == 0 {
                    v___x_6991_ = v___x_6988_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6992_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6992_, 0, v_a_6985_);
                    lean_ctor_set(v_reuseFailAlloc_6992_, 1, v_a_6986_);
                    v___x_6991_ = v_reuseFailAlloc_6992_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6991_;
            }
            23 => {
                if v_isShared_6998_ == 0 {
                    v___x_7000_ = v___x_6997_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7001_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7001_, 0, v_a_6994_);
                    lean_ctor_set(v_reuseFailAlloc_7001_, 1, v_a_6995_);
                    v___x_7000_ = v_reuseFailAlloc_7001_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(
    mut v___x_7003_: *mut LeanObject,
    mut v___x_7004_: *mut LeanObject,
    mut v_self_7005_: *mut LeanObject,
    mut v_dir_7006_: *mut LeanObject,
    mut v_targetDecls_7007_: *mut LeanObject,
    mut v_pkg_7008_: *mut LeanObject,
    mut v_name_7009_: *mut LeanObject,
    mut v_config_7010_: *mut LeanObject,
    mut v_config_7011_: *mut LeanObject,
    mut v___y_7012_: *mut LeanObject,
    mut v___y_7013_: *mut LeanObject,
    mut v___y_7014_: *mut LeanObject,
    mut v___y_7015_: *mut LeanObject,
    mut v___y_7016_: *mut LeanObject,
    mut v___y_7017_: *mut LeanObject,
    mut v___y_7018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7019_: *mut LeanObject = core::ptr::null_mut();
    v_res_7019_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(
        v___x_7003_,
        v___x_7004_,
        v_self_7005_,
        v_dir_7006_,
        v_targetDecls_7007_,
        v_pkg_7008_,
        v_name_7009_,
        v_config_7010_,
        v_config_7011_,
        v___y_7012_,
        v___y_7013_,
        v___y_7014_,
        v___y_7015_,
        v___y_7016_,
        v___y_7017_,
    );
    lean_dec_ref(v___y_7016_);
    lean_dec(v___y_7015_);
    lean_dec(v___y_7014_);
    lean_dec(v___y_7013_);
    lean_dec(v_config_7011_);
    lean_dec_ref(v_targetDecls_7007_);
    return v_res_7019_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(
    mut v_self_7021_: *mut LeanObject,
    mut v_a_7022_: *mut LeanObject,
    mut v_a_7023_: *mut LeanObject,
    mut v_a_7024_: *mut LeanObject,
    mut v_a_7025_: *mut LeanObject,
    mut v_a_7026_: *mut LeanObject,
    mut v_a_7027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7048_: u8 = 0;
    let mut v_task_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7053_: u8 = 0;
    let mut v_registeredJobs_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: u8 = 0;
    let mut v___x_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: u8 = 0;
    let mut v_job_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7071_: u8 = 0;
    let mut v_unused_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_7029_ = lean_ctor_get(v_self_7021_, 0);
                lean_inc_ref_n(v_pkg_7029_, 2);
                v_name_7030_ = lean_ctor_get(v_self_7021_, 1);
                lean_inc_n(v_name_7030_, 3);
                v_config_7031_ = lean_ctor_get(v_self_7021_, 2);
                lean_inc(v_config_7031_);
                v_keyName_7032_ = lean_ctor_get(v_pkg_7029_, 2);
                v_dir_7033_ = lean_ctor_get(v_pkg_7029_, 4);
                lean_inc_ref(v_dir_7033_);
                v_config_7034_ = lean_ctor_get(v_pkg_7029_, 6);
                lean_inc_ref(v_config_7034_);
                v_targetDecls_7035_ = lean_ctor_get(v_pkg_7029_, 14);
                lean_inc_ref(v_targetDecls_7035_);
                v___x_7036_ = l_Lake_instDataKindDynlib;
                v___x_7037_ = l_Lake_LeanLib_modulesFacet;
                lean_inc(v_keyName_7032_);
                v___x_7038_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_7038_, 0, v_keyName_7032_);
                lean_ctor_set(v___x_7038_, 1, v_name_7030_);
                v___x_7039_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
                lean_inc_ref(v_self_7021_);
                v___x_7040_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_7040_, 0, v___x_7038_);
                lean_ctor_set(v___x_7040_, 1, v___x_7039_);
                lean_ctor_set(v___x_7040_, 2, v_self_7021_);
                lean_ctor_set(v___x_7040_, 3, v___x_7037_);
                v___x_7041_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7041_, 0, v_pkg_7029_);
                v___f_7042_ = lean_alloc_closure(
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed
                        as *mut core::ffi::c_void,
                    16,
                    9,
                );
                lean_closure_set(v___f_7042_, 0, v___x_7040_);
                lean_closure_set(v___f_7042_, 1, v___x_7041_);
                lean_closure_set(v___f_7042_, 2, v_self_7021_);
                lean_closure_set(v___f_7042_, 3, v_dir_7033_);
                lean_closure_set(v___f_7042_, 4, v_targetDecls_7035_);
                lean_closure_set(v___f_7042_, 5, v_pkg_7029_);
                lean_closure_set(v___f_7042_, 6, v_name_7030_);
                lean_closure_set(v___f_7042_, 7, v_config_7034_);
                lean_closure_set(v___f_7042_, 8, v_config_7031_);
                v___x_7043_ = l_Lake_ensureJob___redArg(
                    v___x_7036_,
                    v___f_7042_,
                    v_a_7022_,
                    v_a_7023_,
                    v_a_7024_,
                    v_a_7025_,
                    v_a_7026_,
                    v_a_7027_,
                );
                if lean_obj_tag(v___x_7043_) == 0 {
                    v_a_7044_ = lean_ctor_get(v___x_7043_, 0);
                    v_a_7045_ = lean_ctor_get(v___x_7043_, 1);
                    v_isSharedCheck_7073_ = (!lean_is_exclusive(v___x_7043_)) as u8;
                    if v_isSharedCheck_7073_ == 0 {
                        v___x_7047_ = v___x_7043_;
                        v_isShared_7048_ = v_isSharedCheck_7073_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7045_);
                        lean_inc(v_a_7044_);
                        lean_dec(v___x_7043_);
                        v___x_7047_ = lean_box(0);
                        v_isShared_7048_ = v_isSharedCheck_7073_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_7030_);
                    return v___x_7043_;
                }
            }
            1 => {
                v_task_7049_ = lean_ctor_get(v_a_7044_, 0);
                v_kind_7050_ = lean_ctor_get(v_a_7044_, 1);
                v_isSharedCheck_7071_ = (!lean_is_exclusive(v_a_7044_)) as u8;
                if v_isSharedCheck_7071_ == 0 {
                    v_unused_7072_ = lean_ctor_get(v_a_7044_, 2);
                    lean_dec(v_unused_7072_);
                    v___x_7052_ = v_a_7044_;
                    v_isShared_7053_ = v_isSharedCheck_7071_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_7050_);
                    lean_inc(v_task_7049_);
                    lean_dec(v_a_7044_);
                    v___x_7052_ = lean_box(0);
                    v_isShared_7053_ = v_isSharedCheck_7071_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_7054_ = lean_ctor_get(v_a_7026_, 3);
                v___x_7055_ = lean_st_ref_take(v_registeredJobs_7054_);
                v___x_7056_ = 1;
                v___x_7057_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_7030_,
                    v___x_7056_,
                );
                v___x_7058_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0;
                v___x_7059_ = lean_string_append(v___x_7057_, v___x_7058_);
                v___x_7060_ = 0;
                if v_isShared_7053_ == 0 {
                    lean_ctor_set(v___x_7052_, 2, v___x_7059_);
                    v_job_7062_ = v___x_7052_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7070_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7070_, 0, v_task_7049_);
                    lean_ctor_set(v_reuseFailAlloc_7070_, 1, v_kind_7050_);
                    lean_ctor_set(v_reuseFailAlloc_7070_, 2, v___x_7059_);
                    v_job_7062_ = v_reuseFailAlloc_7070_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_7062_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_7060_,
                );
                lean_inc_ref(v_job_7062_);
                v___x_7063_ = l_Lake_Job_toOpaque___redArg(v_job_7062_);
                v___x_7064_ = lean_array_push(v___x_7055_, v___x_7063_);
                v___x_7065_ = lean_st_ref_set(v_registeredJobs_7054_, v___x_7064_);
                v___x_7066_ = l_Lake_Job_renew___redArg(v_job_7062_);
                if v_isShared_7048_ == 0 {
                    lean_ctor_set(v___x_7047_, 0, v___x_7066_);
                    v___x_7068_ = v___x_7047_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7069_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___x_7066_);
                    lean_ctor_set(v_reuseFailAlloc_7069_, 1, v_a_7045_);
                    v___x_7068_ = v_reuseFailAlloc_7069_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(
    mut v_self_7074_: *mut LeanObject,
    mut v_a_7075_: *mut LeanObject,
    mut v_a_7076_: *mut LeanObject,
    mut v_a_7077_: *mut LeanObject,
    mut v_a_7078_: *mut LeanObject,
    mut v_a_7079_: *mut LeanObject,
    mut v_a_7080_: *mut LeanObject,
    mut v_a_7081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7082_: *mut LeanObject = core::ptr::null_mut();
    v_res_7082_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(
        v_self_7074_,
        v_a_7075_,
        v_a_7076_,
        v_a_7077_,
        v_a_7078_,
        v_a_7079_,
        v_a_7080_,
    );
    lean_dec_ref(v_a_7079_);
    lean_dec(v_a_7078_);
    lean_dec(v_a_7077_);
    lean_dec(v_a_7076_);
    return v_res_7082_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(
    mut v_fmt_7083_: u8,
    mut v_a_7084_: *mut LeanObject,
) -> *mut LeanObject {
    if v_fmt_7083_ == 0 {
        let mut v_path_7085_: *mut LeanObject = core::ptr::null_mut();
        v_path_7085_ = lean_ctor_get(v_a_7084_, 0);
        lean_inc_ref(v_path_7085_);
        return v_path_7085_;
    } else {
        let mut v_path_7086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
        v_path_7086_ = lean_ctor_get(v_a_7084_, 0);
        lean_inc_ref(v_path_7086_);
        v___x_7087_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_7087_, 0, v_path_7086_);
        v___x_7088_ = l_Lean_Json_compress(v___x_7087_);
        return v___x_7088_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(
    mut v_fmt_7089_: *mut LeanObject,
    mut v_a_7090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_7091_: u8 = 0;
    let mut v_res_7092_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_7091_ = (lean_unbox(v_fmt_7089_) as u8);
    v_res_7092_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(
        v_fmt_boxed_7091_,
        v_a_7090_,
    );
    lean_dec_ref(v_a_7090_);
    return v_res_7092_;
}
pub unsafe fn _init_l_Lake_LeanLib_sharedFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___f_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: u8 = 0;
    let mut v___x_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    v___f_7095_ = l_Lake_LeanLib_sharedFacetConfig___closed__0;
    v___x_7096_ = 1;
    v___x_7097_ = l_Lake_instDataKindDynlib;
    v___x_7098_ = l_Lake_LeanLib_sharedFacetConfig___closed__1;
    v___x_7099_ = l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
    v___x_7100_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_7100_, 0, v___x_7099_);
    lean_ctor_set(v___x_7100_, 1, v___x_7098_);
    lean_ctor_set(v___x_7100_, 2, v___x_7097_);
    lean_ctor_set(v___x_7100_, 3, v___f_7095_);
    lean_ctor_set_uint8(
        v___x_7100_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_7096_,
    );
    lean_ctor_set_uint8(
        v___x_7100_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_7096_,
    );
    return v___x_7100_;
}
pub unsafe fn _init_l_Lake_LeanLib_sharedFacetConfig() -> *mut LeanObject {
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    v___x_7101_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_sharedFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_sharedFacetConfig___closed__2_once),
        _init_l_Lake_LeanLib_sharedFacetConfig___closed__2,
    );
    return v___x_7101_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(
    mut v___x_7102_: *mut LeanObject,
    mut v_as_7103_: *mut LeanObject,
    mut v_sz_7104_: usize,
    mut v_i_7105_: usize,
    mut v_b_7106_: *mut LeanObject,
    mut v___y_7107_: *mut LeanObject,
    mut v___y_7108_: *mut LeanObject,
    mut v___y_7109_: *mut LeanObject,
    mut v___y_7110_: *mut LeanObject,
    mut v___y_7111_: *mut LeanObject,
    mut v___y_7112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7114_: u8 = 0;
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: usize = 0;
    let mut v___x_7124_: usize = 0;
    let mut v_a_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7130_: u8 = 0;
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7114_ = lean_usize_dec_lt(v_i_7105_, v_sz_7104_);
                if v___x_7114_ == 0 {
                    lean_dec_ref(v___y_7107_);
                    lean_dec_ref(v___x_7102_);
                    v___x_7115_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7115_, 0, v_b_7106_);
                    lean_ctor_set(v___x_7115_, 1, v___y_7112_);
                    return v___x_7115_;
                } else {
                    v_a_7116_ = lean_array_uget_borrowed(v_as_7103_, v_i_7105_);
                    lean_inc_ref(v___y_7107_);
                    lean_inc_n(v_a_7116_, 2);
                    lean_inc_ref(v___x_7102_);
                    v___x_7117_ =
                        l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
                            v___x_7102_,
                            v_a_7116_,
                            v_a_7116_,
                            v___x_7114_,
                            v___y_7107_,
                            v___y_7108_,
                            v___y_7109_,
                            v___y_7110_,
                            v___y_7111_,
                            v___y_7112_,
                        );
                    if lean_obj_tag(v___x_7117_) == 0 {
                        v_a_7118_ = lean_ctor_get(v___x_7117_, 0);
                        lean_inc(v_a_7118_);
                        v_a_7119_ = lean_ctor_get(v___x_7117_, 1);
                        lean_inc(v_a_7119_);
                        lean_dec_ref_known(v___x_7117_, 2);
                        v_snd_7120_ = lean_ctor_get(v_a_7118_, 1);
                        lean_inc(v_snd_7120_);
                        lean_dec(v_a_7118_);
                        v___x_7121_ = l_Lake_Job_toOpaque___redArg(v_snd_7120_);
                        v___x_7122_ = l_Lake_Job_mix___redArg(v_b_7106_, v___x_7121_);
                        v___x_7123_ = 1usize;
                        v___x_7124_ = lean_usize_add(v_i_7105_, v___x_7123_);
                        v_i_7105_ = v___x_7124_;
                        v_b_7106_ = v___x_7122_;
                        v___y_7112_ = v_a_7119_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_7107_);
                        lean_dec_ref(v_b_7106_);
                        lean_dec_ref(v___x_7102_);
                        v_a_7126_ = lean_ctor_get(v___x_7117_, 0);
                        v_a_7127_ = lean_ctor_get(v___x_7117_, 1);
                        v_isSharedCheck_7134_ = (!lean_is_exclusive(v___x_7117_)) as u8;
                        if v_isSharedCheck_7134_ == 0 {
                            v___x_7129_ = v___x_7117_;
                            v_isShared_7130_ = v_isSharedCheck_7134_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7127_);
                            lean_inc(v_a_7126_);
                            lean_dec(v___x_7117_);
                            v___x_7129_ = lean_box(0);
                            v_isShared_7130_ = v_isSharedCheck_7134_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7130_ == 0 {
                    v___x_7132_ = v___x_7129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7133_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7133_, 0, v_a_7126_);
                    lean_ctor_set(v_reuseFailAlloc_7133_, 1, v_a_7127_);
                    v___x_7132_ = v_reuseFailAlloc_7133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(
    mut v___x_7135_: *mut LeanObject,
    mut v_as_7136_: *mut LeanObject,
    mut v_sz_7137_: *mut LeanObject,
    mut v_i_7138_: *mut LeanObject,
    mut v_b_7139_: *mut LeanObject,
    mut v___y_7140_: *mut LeanObject,
    mut v___y_7141_: *mut LeanObject,
    mut v___y_7142_: *mut LeanObject,
    mut v___y_7143_: *mut LeanObject,
    mut v___y_7144_: *mut LeanObject,
    mut v___y_7145_: *mut LeanObject,
    mut v___y_7146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7147_: usize = 0;
    let mut v_i_boxed_7148_: usize = 0;
    let mut v_res_7149_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7147_ = lean_unbox_usize(v_sz_7137_);
    lean_dec(v_sz_7137_);
    v_i_boxed_7148_ = lean_unbox_usize(v_i_7138_);
    lean_dec(v_i_7138_);
    v_res_7149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_7135_, v_as_7136_, v_sz_boxed_7147_, v_i_boxed_7148_, v_b_7139_, v___y_7140_, v___y_7141_, v___y_7142_, v___y_7143_, v___y_7144_, v___y_7145_);
    lean_dec_ref(v___y_7144_);
    lean_dec(v___y_7143_);
    lean_dec(v___y_7142_);
    lean_dec(v___y_7141_);
    lean_dec_ref(v_as_7136_);
    return v_res_7149_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(
    mut v___x_7150_: *mut LeanObject,
    mut v_as_7151_: *mut LeanObject,
    mut v_sz_7152_: usize,
    mut v_i_7153_: usize,
    mut v_b_7154_: *mut LeanObject,
    mut v___y_7155_: *mut LeanObject,
    mut v___y_7156_: *mut LeanObject,
    mut v___y_7157_: *mut LeanObject,
    mut v___y_7158_: *mut LeanObject,
    mut v___y_7159_: *mut LeanObject,
    mut v___y_7160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7162_: u8 = 0;
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: usize = 0;
    let mut v___x_7170_: usize = 0;
    let mut v_a_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7176_: u8 = 0;
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7162_ = lean_usize_dec_lt(v_i_7153_, v_sz_7152_);
                if v___x_7162_ == 0 {
                    lean_dec_ref(v___y_7155_);
                    lean_dec_ref(v___x_7150_);
                    v___x_7163_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7163_, 0, v_b_7154_);
                    lean_ctor_set(v___x_7163_, 1, v___y_7160_);
                    return v___x_7163_;
                } else {
                    v_a_7164_ = lean_array_uget_borrowed(v_as_7151_, v_i_7153_);
                    lean_inc_ref(v___y_7155_);
                    lean_inc(v_a_7164_);
                    lean_inc_ref(v___x_7150_);
                    v___x_7165_ = l_Lake_Package_fetchTargetJob(
                        v___x_7150_,
                        v_a_7164_,
                        v___y_7155_,
                        v___y_7156_,
                        v___y_7157_,
                        v___y_7158_,
                        v___y_7159_,
                        v___y_7160_,
                    );
                    if lean_obj_tag(v___x_7165_) == 0 {
                        v_a_7166_ = lean_ctor_get(v___x_7165_, 0);
                        lean_inc(v_a_7166_);
                        v_a_7167_ = lean_ctor_get(v___x_7165_, 1);
                        lean_inc(v_a_7167_);
                        lean_dec_ref_known(v___x_7165_, 2);
                        v___x_7168_ = l_Lake_Job_mix___redArg(v_b_7154_, v_a_7166_);
                        v___x_7169_ = 1usize;
                        v___x_7170_ = lean_usize_add(v_i_7153_, v___x_7169_);
                        v_i_7153_ = v___x_7170_;
                        v_b_7154_ = v___x_7168_;
                        v___y_7160_ = v_a_7167_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_7155_);
                        lean_dec_ref(v_b_7154_);
                        lean_dec_ref(v___x_7150_);
                        v_a_7172_ = lean_ctor_get(v___x_7165_, 0);
                        v_a_7173_ = lean_ctor_get(v___x_7165_, 1);
                        v_isSharedCheck_7180_ = (!lean_is_exclusive(v___x_7165_)) as u8;
                        if v_isSharedCheck_7180_ == 0 {
                            v___x_7175_ = v___x_7165_;
                            v_isShared_7176_ = v_isSharedCheck_7180_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7173_);
                            lean_inc(v_a_7172_);
                            lean_dec(v___x_7165_);
                            v___x_7175_ = lean_box(0);
                            v_isShared_7176_ = v_isSharedCheck_7180_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7176_ == 0 {
                    v___x_7178_ = v___x_7175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7179_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7179_, 0, v_a_7172_);
                    lean_ctor_set(v_reuseFailAlloc_7179_, 1, v_a_7173_);
                    v___x_7178_ = v_reuseFailAlloc_7179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(
    mut v___x_7181_: *mut LeanObject,
    mut v_as_7182_: *mut LeanObject,
    mut v_sz_7183_: *mut LeanObject,
    mut v_i_7184_: *mut LeanObject,
    mut v_b_7185_: *mut LeanObject,
    mut v___y_7186_: *mut LeanObject,
    mut v___y_7187_: *mut LeanObject,
    mut v___y_7188_: *mut LeanObject,
    mut v___y_7189_: *mut LeanObject,
    mut v___y_7190_: *mut LeanObject,
    mut v___y_7191_: *mut LeanObject,
    mut v___y_7192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7193_: usize = 0;
    let mut v_i_boxed_7194_: usize = 0;
    let mut v_res_7195_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7193_ = lean_unbox_usize(v_sz_7183_);
    lean_dec(v_sz_7183_);
    v_i_boxed_7194_ = lean_unbox_usize(v_i_7184_);
    lean_dec(v_i_7184_);
    v_res_7195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_7181_, v_as_7182_, v_sz_boxed_7193_, v_i_boxed_7194_, v_b_7185_, v___y_7186_, v___y_7187_, v___y_7188_, v___y_7189_, v___y_7190_, v___y_7191_);
    lean_dec_ref(v___y_7190_);
    lean_dec(v___y_7189_);
    lean_dec(v___y_7188_);
    lean_dec(v___y_7187_);
    lean_dec_ref(v_as_7182_);
    return v_res_7195_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(
    mut v_self_7198_: *mut LeanObject,
    mut v_a_7199_: *mut LeanObject,
    mut v_a_7200_: *mut LeanObject,
    mut v_a_7201_: *mut LeanObject,
    mut v_a_7202_: *mut LeanObject,
    mut v_a_7203_: *mut LeanObject,
    mut v_a_7204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7220_: u8 = 0;
    let mut v___x_7221_: u8 = 0;
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: u8 = 0;
    let mut v___x_7234_: u8 = 0;
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7245_: usize = 0;
    let mut v___x_7246_: usize = 0;
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7250_: usize = 0;
    let mut v___x_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_7206_ = lean_ctor_get(v_self_7198_, 0);
                lean_inc_ref_n(v_pkg_7206_, 2);
                v_name_7207_ = lean_ctor_get(v_self_7198_, 1);
                lean_inc(v_name_7207_);
                v_config_7208_ = lean_ctor_get(v_self_7198_, 2);
                lean_inc(v_config_7208_);
                lean_dec_ref(v_self_7198_);
                v_baseName_7209_ = lean_ctor_get(v_pkg_7206_, 1);
                v_keyName_7210_ = lean_ctor_get(v_pkg_7206_, 2);
                v___x_7211_ = l_Lake_Package_extraDepFacet;
                lean_inc(v_keyName_7210_);
                v___x_7212_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7212_, 0, v_keyName_7210_);
                v___x_7213_ = l_Lake_Package_keyword;
                v___x_7214_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_7214_, 0, v___x_7212_);
                lean_ctor_set(v___x_7214_, 1, v___x_7213_);
                lean_ctor_set(v___x_7214_, 2, v_pkg_7206_);
                lean_ctor_set(v___x_7214_, 3, v___x_7211_);
                lean_inc_ref(v_a_7199_);
                lean_inc_ref(v_a_7203_);
                lean_inc(v_a_7202_);
                lean_inc(v_a_7201_);
                lean_inc(v_a_7200_);
                v___x_7215_ = lean_apply_7(
                    v_a_7199_,
                    v___x_7214_,
                    v_a_7200_,
                    v_a_7201_,
                    v_a_7202_,
                    v_a_7203_,
                    v_a_7204_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_7215_) == 0 {
                    v_a_7216_ = lean_ctor_get(v___x_7215_, 0);
                    v_a_7217_ = lean_ctor_get(v___x_7215_, 1);
                    v_isSharedCheck_7253_ = (!lean_is_exclusive(v___x_7215_)) as u8;
                    if v_isSharedCheck_7253_ == 0 {
                        v___x_7219_ = v___x_7215_;
                        v_isShared_7220_ = v_isSharedCheck_7253_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7217_);
                        lean_inc(v_a_7216_);
                        lean_dec(v___x_7215_);
                        v___x_7219_ = lean_box(0);
                        v_isShared_7220_ = v_isSharedCheck_7253_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_config_7208_);
                    lean_dec(v_name_7207_);
                    lean_dec_ref(v_pkg_7206_);
                    lean_dec_ref(v_a_7199_);
                    return v___x_7215_;
                }
            }
            1 => {
                v___x_7221_ = 1;
                lean_inc(v_baseName_7209_);
                v___x_7222_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_7209_,
                    v___x_7221_,
                );
                v___x_7223_ = lean_unsigned_to_nat(0);
                v___x_7224_ =
                    l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0;
                v_needs_7225_ = lean_ctor_get(v_config_7208_, 5);
                lean_inc_ref(v_needs_7225_);
                v_extraDepTargets_7226_ = lean_ctor_get(v_config_7208_, 6);
                lean_inc_ref(v_extraDepTargets_7226_);
                lean_dec(v_config_7208_);
                v___x_7227_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0;
                v___x_7228_ = lean_string_append(v___x_7222_, v___x_7227_);
                v___x_7229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_7207_,
                    v___x_7221_,
                );
                v___x_7230_ = lean_string_append(v___x_7228_, v___x_7229_);
                lean_dec_ref(v___x_7229_);
                v___x_7231_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1;
                v___x_7232_ = lean_string_append(v___x_7230_, v___x_7231_);
                v___x_7233_ = 0;
                v___x_7234_ = 0;
                v___x_7235_ = l_Lake_BuildTrace_nil(v___x_7232_);
                v___x_7236_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_7236_, 0, v___x_7224_);
                lean_ctor_set(v___x_7236_, 1, v___x_7235_);
                lean_ctor_set(v___x_7236_, 2, v___x_7223_);
                lean_ctor_set_uint8(
                    v___x_7236_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_7233_,
                );
                lean_ctor_set_uint8(
                    v___x_7236_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_7234_,
                );
                v___x_7237_ = lean_box(0);
                v___x_7238_ = lean_box(0);
                if v_isShared_7220_ == 0 {
                    lean_ctor_set(v___x_7219_, 1, v___x_7236_);
                    lean_ctor_set(v___x_7219_, 0, v___x_7238_);
                    v___x_7240_ = v___x_7219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7252_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7252_, 0, v___x_7238_);
                    lean_ctor_set(v_reuseFailAlloc_7252_, 1, v___x_7236_);
                    v___x_7240_ = v_reuseFailAlloc_7252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7241_ = lean_task_pure(v___x_7240_);
                v___x_7242_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0;
                v_job_7243_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v_job_7243_, 0, v___x_7241_);
                lean_ctor_set(v_job_7243_, 1, v___x_7237_);
                lean_ctor_set(v_job_7243_, 2, v___x_7242_);
                lean_ctor_set_uint8(
                    v_job_7243_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_7234_,
                );
                v___x_7244_ = l_Lake_Job_mix___redArg(v_job_7243_, v_a_7216_);
                v_sz_7245_ = lean_array_size(v_extraDepTargets_7226_);
                v___x_7246_ = 0usize;
                lean_inc_ref(v_a_7199_);
                lean_inc_ref(v_pkg_7206_);
                v___x_7247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_7206_, v_extraDepTargets_7226_, v_sz_7245_, v___x_7246_, v___x_7244_, v_a_7199_, v_a_7200_, v_a_7201_, v_a_7202_, v_a_7203_, v_a_7217_);
                lean_dec_ref(v_extraDepTargets_7226_);
                if lean_obj_tag(v___x_7247_) == 0 {
                    v_a_7248_ = lean_ctor_get(v___x_7247_, 0);
                    lean_inc(v_a_7248_);
                    v_a_7249_ = lean_ctor_get(v___x_7247_, 1);
                    lean_inc(v_a_7249_);
                    lean_dec_ref_known(v___x_7247_, 2);
                    v_sz_7250_ = lean_array_size(v_needs_7225_);
                    v___x_7251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_7206_, v_needs_7225_, v_sz_7250_, v___x_7246_, v_a_7248_, v_a_7199_, v_a_7200_, v_a_7201_, v_a_7202_, v_a_7203_, v_a_7249_);
                    lean_dec_ref(v_needs_7225_);
                    return v___x_7251_;
                } else {
                    lean_dec_ref(v_needs_7225_);
                    lean_dec_ref(v_pkg_7206_);
                    lean_dec_ref(v_a_7199_);
                    return v___x_7247_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(
    mut v_self_7254_: *mut LeanObject,
    mut v_a_7255_: *mut LeanObject,
    mut v_a_7256_: *mut LeanObject,
    mut v_a_7257_: *mut LeanObject,
    mut v_a_7258_: *mut LeanObject,
    mut v_a_7259_: *mut LeanObject,
    mut v_a_7260_: *mut LeanObject,
    mut v_a_7261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7262_: *mut LeanObject = core::ptr::null_mut();
    v_res_7262_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(
        v_self_7254_,
        v_a_7255_,
        v_a_7256_,
        v_a_7257_,
        v_a_7258_,
        v_a_7259_,
        v_a_7260_,
    );
    lean_dec_ref(v_a_7259_);
    lean_dec(v_a_7258_);
    lean_dec(v_a_7257_);
    lean_dec(v_a_7256_);
    return v_res_7262_;
}
pub unsafe fn _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___f_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: u8 = 0;
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut LeanObject = core::ptr::null_mut();
    v___f_7264_ = l_Lake_LeanLib_leanArtsFacetConfig___closed__0;
    v___x_7265_ = 1;
    v___x_7266_ = l_Lake_instDataKindUnit;
    v___x_7267_ = l_Lake_LeanLib_extraDepFacetConfig___closed__0;
    v___x_7268_ = l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
    v___x_7269_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_7269_, 0, v___x_7268_);
    lean_ctor_set(v___x_7269_, 1, v___x_7267_);
    lean_ctor_set(v___x_7269_, 2, v___x_7266_);
    lean_ctor_set(v___x_7269_, 3, v___f_7264_);
    lean_ctor_set_uint8(
        v___x_7269_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_7265_,
    );
    lean_ctor_set_uint8(
        v___x_7269_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_7265_,
    );
    return v___x_7269_;
}
pub unsafe fn _init_l_Lake_LeanLib_extraDepFacetConfig() -> *mut LeanObject {
    let mut v___x_7270_: *mut LeanObject = core::ptr::null_mut();
    v___x_7270_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_extraDepFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_extraDepFacetConfig___closed__1_once),
        _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1,
    );
    return v___x_7270_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(
    mut v_self_7271_: *mut LeanObject,
    mut v_sz_7272_: usize,
    mut v_i_7273_: usize,
    mut v_bs_7274_: *mut LeanObject,
    mut v___y_7275_: *mut LeanObject,
    mut v___y_7276_: *mut LeanObject,
    mut v___y_7277_: *mut LeanObject,
    mut v___y_7278_: *mut LeanObject,
    mut v___y_7279_: *mut LeanObject,
    mut v___y_7280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7282_: u8 = 0;
    let mut v___x_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: usize = 0;
    let mut v___x_7298_: usize = 0;
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7305_: u8 = 0;
    let mut v___x_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7282_ = lean_usize_dec_lt(v_i_7273_, v_sz_7272_);
                if v___x_7282_ == 0 {
                    lean_dec_ref(v___y_7275_);
                    lean_dec_ref(v_self_7271_);
                    v___x_7283_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7283_, 0, v_bs_7274_);
                    lean_ctor_set(v___x_7283_, 1, v___y_7280_);
                    return v___x_7283_;
                } else {
                    v_pkg_7284_ = lean_ctor_get(v_self_7271_, 0);
                    v_name_7285_ = lean_ctor_get(v_self_7271_, 1);
                    v_keyName_7286_ = lean_ctor_get(v_pkg_7284_, 2);
                    v_v_7287_ = lean_array_uget_borrowed(v_bs_7274_, v_i_7273_);
                    lean_inc(v_name_7285_);
                    lean_inc(v_keyName_7286_);
                    v___x_7288_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v___x_7288_, 0, v_keyName_7286_);
                    lean_ctor_set(v___x_7288_, 1, v_name_7285_);
                    v___x_7289_ = l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
                    lean_inc(v_v_7287_);
                    lean_inc_ref(v_self_7271_);
                    v___x_7290_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v___x_7290_, 0, v___x_7288_);
                    lean_ctor_set(v___x_7290_, 1, v___x_7289_);
                    lean_ctor_set(v___x_7290_, 2, v_self_7271_);
                    lean_ctor_set(v___x_7290_, 3, v_v_7287_);
                    lean_inc_ref(v___y_7275_);
                    lean_inc_ref(v___y_7279_);
                    lean_inc(v___y_7278_);
                    lean_inc(v___y_7277_);
                    lean_inc(v___y_7276_);
                    v___x_7291_ = lean_apply_7(
                        v___y_7275_,
                        v___x_7290_,
                        v___y_7276_,
                        v___y_7277_,
                        v___y_7278_,
                        v___y_7279_,
                        v___y_7280_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_7291_) == 0 {
                        v_a_7292_ = lean_ctor_get(v___x_7291_, 0);
                        lean_inc(v_a_7292_);
                        v_a_7293_ = lean_ctor_get(v___x_7291_, 1);
                        lean_inc(v_a_7293_);
                        lean_dec_ref_known(v___x_7291_, 2);
                        v___x_7294_ = lean_unsigned_to_nat(0);
                        v_bs_x27_7295_ = lean_array_uset(v_bs_7274_, v_i_7273_, v___x_7294_);
                        v___x_7296_ = l_Lake_Job_toOpaque___redArg(v_a_7292_);
                        v___x_7297_ = 1usize;
                        v___x_7298_ = lean_usize_add(v_i_7273_, v___x_7297_);
                        v___x_7299_ = lean_array_uset(v_bs_x27_7295_, v_i_7273_, v___x_7296_);
                        v_i_7273_ = v___x_7298_;
                        v_bs_7274_ = v___x_7299_;
                        v___y_7280_ = v_a_7293_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_7275_);
                        lean_dec_ref(v_bs_7274_);
                        lean_dec_ref(v_self_7271_);
                        v_a_7301_ = lean_ctor_get(v___x_7291_, 0);
                        v_a_7302_ = lean_ctor_get(v___x_7291_, 1);
                        v_isSharedCheck_7309_ = (!lean_is_exclusive(v___x_7291_)) as u8;
                        if v_isSharedCheck_7309_ == 0 {
                            v___x_7304_ = v___x_7291_;
                            v_isShared_7305_ = v_isSharedCheck_7309_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7302_);
                            lean_inc(v_a_7301_);
                            lean_dec(v___x_7291_);
                            v___x_7304_ = lean_box(0);
                            v_isShared_7305_ = v_isSharedCheck_7309_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7305_ == 0 {
                    v___x_7307_ = v___x_7304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7308_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7308_, 0, v_a_7301_);
                    lean_ctor_set(v_reuseFailAlloc_7308_, 1, v_a_7302_);
                    v___x_7307_ = v_reuseFailAlloc_7308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(
    mut v_self_7310_: *mut LeanObject,
    mut v_sz_7311_: *mut LeanObject,
    mut v_i_7312_: *mut LeanObject,
    mut v_bs_7313_: *mut LeanObject,
    mut v___y_7314_: *mut LeanObject,
    mut v___y_7315_: *mut LeanObject,
    mut v___y_7316_: *mut LeanObject,
    mut v___y_7317_: *mut LeanObject,
    mut v___y_7318_: *mut LeanObject,
    mut v___y_7319_: *mut LeanObject,
    mut v___y_7320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7321_: usize = 0;
    let mut v_i_boxed_7322_: usize = 0;
    let mut v_res_7323_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7321_ = lean_unbox_usize(v_sz_7311_);
    lean_dec(v_sz_7311_);
    v_i_boxed_7322_ = lean_unbox_usize(v_i_7312_);
    lean_dec(v_i_7312_);
    v_res_7323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_7310_, v_sz_boxed_7321_, v_i_boxed_7322_, v_bs_7313_, v___y_7314_, v___y_7315_, v___y_7316_, v___y_7317_, v___y_7318_, v___y_7319_);
    lean_dec_ref(v___y_7318_);
    lean_dec(v___y_7317_);
    lean_dec(v___y_7316_);
    lean_dec(v___y_7315_);
    return v_res_7323_;
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(
    mut v_self_7325_: *mut LeanObject,
    mut v_a_7326_: *mut LeanObject,
    mut v_a_7327_: *mut LeanObject,
    mut v_a_7328_: *mut LeanObject,
    mut v_a_7329_: *mut LeanObject,
    mut v_a_7330_: *mut LeanObject,
    mut v_a_7331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defaultFacets_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7335_: usize = 0;
    let mut v___x_7336_: usize = 0;
    let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7342_: u8 = 0;
    let mut v___x_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7348_: u8 = 0;
    let mut v_a_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7353_: u8 = 0;
    let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_7333_ = lean_ctor_get(v_self_7325_, 2);
                v_defaultFacets_7334_ = lean_ctor_get(v_config_7333_, 7);
                lean_inc_ref(v_defaultFacets_7334_);
                v_sz_7335_ = lean_array_size(v_defaultFacets_7334_);
                v___x_7336_ = 0usize;
                v___x_7337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_7325_, v_sz_7335_, v___x_7336_, v_defaultFacets_7334_, v_a_7326_, v_a_7327_, v_a_7328_, v_a_7329_, v_a_7330_, v_a_7331_);
                if lean_obj_tag(v___x_7337_) == 0 {
                    v_a_7338_ = lean_ctor_get(v___x_7337_, 0);
                    v_a_7339_ = lean_ctor_get(v___x_7337_, 1);
                    v_isSharedCheck_7348_ = (!lean_is_exclusive(v___x_7337_)) as u8;
                    if v_isSharedCheck_7348_ == 0 {
                        v___x_7341_ = v___x_7337_;
                        v_isShared_7342_ = v_isSharedCheck_7348_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7339_);
                        lean_inc(v_a_7338_);
                        lean_dec(v___x_7337_);
                        v___x_7341_ = lean_box(0);
                        v_isShared_7342_ = v_isSharedCheck_7348_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7349_ = lean_ctor_get(v___x_7337_, 0);
                    v_a_7350_ = lean_ctor_get(v___x_7337_, 1);
                    v_isSharedCheck_7357_ = (!lean_is_exclusive(v___x_7337_)) as u8;
                    if v_isSharedCheck_7357_ == 0 {
                        v___x_7352_ = v___x_7337_;
                        v_isShared_7353_ = v_isSharedCheck_7357_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7350_);
                        lean_inc(v_a_7349_);
                        lean_dec(v___x_7337_);
                        v___x_7352_ = lean_box(0);
                        v_isShared_7353_ = v_isSharedCheck_7357_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7343_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0;
                v___x_7344_ = l_Lake_Job_mixArray___redArg(v_a_7338_, v___x_7343_);
                lean_dec(v_a_7338_);
                if v_isShared_7342_ == 0 {
                    lean_ctor_set(v___x_7341_, 0, v___x_7344_);
                    v___x_7346_ = v___x_7341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7347_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7347_, 0, v___x_7344_);
                    lean_ctor_set(v_reuseFailAlloc_7347_, 1, v_a_7339_);
                    v___x_7346_ = v_reuseFailAlloc_7347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7346_;
            }
            3 => {
                if v_isShared_7353_ == 0 {
                    v___x_7355_ = v___x_7352_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7356_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7356_, 0, v_a_7349_);
                    lean_ctor_set(v_reuseFailAlloc_7356_, 1, v_a_7350_);
                    v___x_7355_ = v_reuseFailAlloc_7356_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(
    mut v_self_7358_: *mut LeanObject,
    mut v_a_7359_: *mut LeanObject,
    mut v_a_7360_: *mut LeanObject,
    mut v_a_7361_: *mut LeanObject,
    mut v_a_7362_: *mut LeanObject,
    mut v_a_7363_: *mut LeanObject,
    mut v_a_7364_: *mut LeanObject,
    mut v_a_7365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7366_: *mut LeanObject = core::ptr::null_mut();
    v_res_7366_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(
        v_self_7358_,
        v_a_7359_,
        v_a_7360_,
        v_a_7361_,
        v_a_7362_,
        v_a_7363_,
        v_a_7364_,
    );
    lean_dec_ref(v_a_7363_);
    lean_dec(v_a_7362_);
    lean_dec(v_a_7361_);
    lean_dec(v_a_7360_);
    return v_res_7366_;
}
pub unsafe fn _init_l_Lake_LeanLib_defaultFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___f_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: u8 = 0;
    let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut LeanObject = core::ptr::null_mut();
    v___f_7368_ = l_Lake_LeanLib_leanArtsFacetConfig___closed__0;
    v___x_7369_ = 1;
    v___x_7370_ = l_Lake_instDataKindUnit;
    v___x_7371_ = l_Lake_LeanLib_defaultFacetConfig___closed__0;
    v___x_7372_ = l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2;
    v___x_7373_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_7373_, 0, v___x_7372_);
    lean_ctor_set(v___x_7373_, 1, v___x_7371_);
    lean_ctor_set(v___x_7373_, 2, v___x_7370_);
    lean_ctor_set(v___x_7373_, 3, v___f_7368_);
    lean_ctor_set_uint8(
        v___x_7373_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_7369_,
    );
    lean_ctor_set_uint8(
        v___x_7373_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_7369_,
    );
    return v___x_7373_;
}
pub unsafe fn _init_l_Lake_LeanLib_defaultFacetConfig() -> *mut LeanObject {
    let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
    v___x_7374_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_defaultFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_defaultFacetConfig___closed__1_once),
        _init_l_Lake_LeanLib_defaultFacetConfig___closed__1,
    );
    return v___x_7374_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
    mut v_k_7375_: *mut LeanObject,
    mut v_v_7376_: *mut LeanObject,
    mut v_t_7377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_7378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7385_: u8 = 0;
    let mut v___x_7386_: u8 = 0;
    let mut v_impl_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: u8 = 0;
    let mut v___x_7398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7405_: u8 = 0;
    let mut v_size_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_7410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: u8 = 0;
    let mut v___x_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7417_: u8 = 0;
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7443_: u8 = 0;
    let mut v_unused_7444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7457_: u8 = 0;
    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7461_: u8 = 0;
    let mut v_unused_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7468_: u8 = 0;
    let mut v_unused_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_7474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7480_: u8 = 0;
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7488_: u8 = 0;
    let mut v_unused_7489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7496_: u8 = 0;
    let mut v_k_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7501_: u8 = 0;
    let mut v___x_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7512_: u8 = 0;
    let mut v_unused_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7516_: u8 = 0;
    let mut v_unused_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: u8 = 0;
    let mut v___x_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7545_: u8 = 0;
    let mut v_size_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7554_: u8 = 0;
    let mut v___x_7556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7557_: u8 = 0;
    let mut v___x_7558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7582_: u8 = 0;
    let mut v_unused_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7595_: u8 = 0;
    let mut v___x_7597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7599_: u8 = 0;
    let mut v_unused_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7606_: u8 = 0;
    let mut v_unused_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7618_: u8 = 0;
    let mut v_k_7619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7623_: u8 = 0;
    let mut v___x_7624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7634_: u8 = 0;
    let mut v_unused_7635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7638_: u8 = 0;
    let mut v_unused_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7646_: u8 = 0;
    let mut v___x_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7654_: u8 = 0;
    let mut v_unused_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7662_: u8 = 0;
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_7377_) == 0 {
                    v_size_7378_ = lean_ctor_get(v_t_7377_, 0);
                    v_k_7379_ = lean_ctor_get(v_t_7377_, 1);
                    v_v_7380_ = lean_ctor_get(v_t_7377_, 2);
                    v_l_7381_ = lean_ctor_get(v_t_7377_, 3);
                    v_r_7382_ = lean_ctor_get(v_t_7377_, 4);
                    v_isSharedCheck_7662_ = (!lean_is_exclusive(v_t_7377_)) as u8;
                    if v_isSharedCheck_7662_ == 0 {
                        v___x_7384_ = v_t_7377_;
                        v_isShared_7385_ = v_isSharedCheck_7662_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_7382_);
                        lean_inc(v_l_7381_);
                        lean_inc(v_v_7380_);
                        lean_inc(v_k_7379_);
                        lean_inc(v_size_7378_);
                        lean_dec(v_t_7377_);
                        v___x_7384_ = lean_box(0);
                        v_isShared_7385_ = v_isSharedCheck_7662_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_7663_ = lean_unsigned_to_nat(1);
                    v___x_7664_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_7664_, 0, v___x_7663_);
                    lean_ctor_set(v___x_7664_, 1, v_k_7375_);
                    lean_ctor_set(v___x_7664_, 2, v_v_7376_);
                    lean_ctor_set(v___x_7664_, 3, v_t_7377_);
                    lean_ctor_set(v___x_7664_, 4, v_t_7377_);
                    return v___x_7664_;
                }
            }
            1 => {
                v___x_7386_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_7375_, v_k_7379_);
                match v___x_7386_ {
                    0 => {
                        lean_dec(v_size_7378_);
                        v_impl_7387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_7375_, v_v_7376_, v_l_7381_);
                        v___x_7388_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_7382_) == 0 {
                            v_size_7389_ = lean_ctor_get(v_r_7382_, 0);
                            v_size_7390_ = lean_ctor_get(v_impl_7387_, 0);
                            lean_inc(v_size_7390_);
                            v_k_7391_ = lean_ctor_get(v_impl_7387_, 1);
                            lean_inc(v_k_7391_);
                            v_v_7392_ = lean_ctor_get(v_impl_7387_, 2);
                            lean_inc(v_v_7392_);
                            v_l_7393_ = lean_ctor_get(v_impl_7387_, 3);
                            lean_inc(v_l_7393_);
                            v_r_7394_ = lean_ctor_get(v_impl_7387_, 4);
                            lean_inc(v_r_7394_);
                            v___x_7395_ = lean_unsigned_to_nat(3);
                            v___x_7396_ = lean_nat_mul(v___x_7395_, v_size_7389_);
                            v___x_7397_ = lean_nat_dec_lt(v___x_7396_, v_size_7390_);
                            lean_dec(v___x_7396_);
                            if v___x_7397_ == 0 {
                                lean_dec(v_r_7394_);
                                lean_dec(v_l_7393_);
                                lean_dec(v_v_7392_);
                                lean_dec(v_k_7391_);
                                v___x_7398_ = lean_nat_add(v___x_7388_, v_size_7390_);
                                lean_dec(v_size_7390_);
                                v___x_7399_ = lean_nat_add(v___x_7398_, v_size_7389_);
                                lean_dec(v___x_7398_);
                                if v_isShared_7385_ == 0 {
                                    lean_ctor_set(v___x_7384_, 3, v_impl_7387_);
                                    lean_ctor_set(v___x_7384_, 0, v___x_7399_);
                                    v___x_7401_ = v___x_7384_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7402_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_7402_, 0, v___x_7399_);
                                    lean_ctor_set(v_reuseFailAlloc_7402_, 1, v_k_7379_);
                                    lean_ctor_set(v_reuseFailAlloc_7402_, 2, v_v_7380_);
                                    lean_ctor_set(v_reuseFailAlloc_7402_, 3, v_impl_7387_);
                                    lean_ctor_set(v_reuseFailAlloc_7402_, 4, v_r_7382_);
                                    v___x_7401_ = v_reuseFailAlloc_7402_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_7468_ = (!lean_is_exclusive(v_impl_7387_)) as u8;
                                if v_isSharedCheck_7468_ == 0 {
                                    v_unused_7469_ = lean_ctor_get(v_impl_7387_, 4);
                                    lean_dec(v_unused_7469_);
                                    v_unused_7470_ = lean_ctor_get(v_impl_7387_, 3);
                                    lean_dec(v_unused_7470_);
                                    v_unused_7471_ = lean_ctor_get(v_impl_7387_, 2);
                                    lean_dec(v_unused_7471_);
                                    v_unused_7472_ = lean_ctor_get(v_impl_7387_, 1);
                                    lean_dec(v_unused_7472_);
                                    v_unused_7473_ = lean_ctor_get(v_impl_7387_, 0);
                                    lean_dec(v_unused_7473_);
                                    v___x_7404_ = v_impl_7387_;
                                    v_isShared_7405_ = v_isSharedCheck_7468_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_7387_);
                                    v___x_7404_ = lean_box(0);
                                    v_isShared_7405_ = v_isSharedCheck_7468_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_7474_ = lean_ctor_get(v_impl_7387_, 3);
                            lean_inc(v_l_7474_);
                            if lean_obj_tag(v_l_7474_) == 0 {
                                v_r_7475_ = lean_ctor_get(v_impl_7387_, 4);
                                v_k_7476_ = lean_ctor_get(v_impl_7387_, 1);
                                v_v_7477_ = lean_ctor_get(v_impl_7387_, 2);
                                v_isSharedCheck_7488_ = (!lean_is_exclusive(v_impl_7387_)) as u8;
                                if v_isSharedCheck_7488_ == 0 {
                                    v_unused_7489_ = lean_ctor_get(v_impl_7387_, 3);
                                    lean_dec(v_unused_7489_);
                                    v_unused_7490_ = lean_ctor_get(v_impl_7387_, 0);
                                    lean_dec(v_unused_7490_);
                                    v___x_7479_ = v_impl_7387_;
                                    v_isShared_7480_ = v_isSharedCheck_7488_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_7475_);
                                    lean_inc(v_v_7477_);
                                    lean_inc(v_k_7476_);
                                    lean_dec(v_impl_7387_);
                                    v___x_7479_ = lean_box(0);
                                    v_isShared_7480_ = v_isSharedCheck_7488_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_7491_ = lean_ctor_get(v_impl_7387_, 4);
                                lean_inc(v_r_7491_);
                                if lean_obj_tag(v_r_7491_) == 0 {
                                    v_k_7492_ = lean_ctor_get(v_impl_7387_, 1);
                                    v_v_7493_ = lean_ctor_get(v_impl_7387_, 2);
                                    v_isSharedCheck_7516_ =
                                        (!lean_is_exclusive(v_impl_7387_)) as u8;
                                    if v_isSharedCheck_7516_ == 0 {
                                        v_unused_7517_ = lean_ctor_get(v_impl_7387_, 4);
                                        lean_dec(v_unused_7517_);
                                        v_unused_7518_ = lean_ctor_get(v_impl_7387_, 3);
                                        lean_dec(v_unused_7518_);
                                        v_unused_7519_ = lean_ctor_get(v_impl_7387_, 0);
                                        lean_dec(v_unused_7519_);
                                        v___x_7495_ = v_impl_7387_;
                                        v_isShared_7496_ = v_isSharedCheck_7516_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_7493_);
                                        lean_inc(v_k_7492_);
                                        lean_dec(v_impl_7387_);
                                        v___x_7495_ = lean_box(0);
                                        v_isShared_7496_ = v_isSharedCheck_7516_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_7520_ = lean_unsigned_to_nat(2);
                                    if v_isShared_7385_ == 0 {
                                        lean_ctor_set(v___x_7384_, 4, v_r_7491_);
                                        lean_ctor_set(v___x_7384_, 3, v_impl_7387_);
                                        lean_ctor_set(v___x_7384_, 0, v___x_7520_);
                                        v___x_7522_ = v___x_7384_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7523_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_7523_, 0, v___x_7520_);
                                        lean_ctor_set(v_reuseFailAlloc_7523_, 1, v_k_7379_);
                                        lean_ctor_set(v_reuseFailAlloc_7523_, 2, v_v_7380_);
                                        lean_ctor_set(v_reuseFailAlloc_7523_, 3, v_impl_7387_);
                                        lean_ctor_set(v_reuseFailAlloc_7523_, 4, v_r_7491_);
                                        v___x_7522_ = v_reuseFailAlloc_7523_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_7380_);
                        lean_dec(v_k_7379_);
                        if v_isShared_7385_ == 0 {
                            lean_ctor_set(v___x_7384_, 2, v_v_7376_);
                            lean_ctor_set(v___x_7384_, 1, v_k_7375_);
                            v___x_7525_ = v___x_7384_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_7526_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7526_, 0, v_size_7378_);
                            lean_ctor_set(v_reuseFailAlloc_7526_, 1, v_k_7375_);
                            lean_ctor_set(v_reuseFailAlloc_7526_, 2, v_v_7376_);
                            lean_ctor_set(v_reuseFailAlloc_7526_, 3, v_l_7381_);
                            lean_ctor_set(v_reuseFailAlloc_7526_, 4, v_r_7382_);
                            v___x_7525_ = v_reuseFailAlloc_7526_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_7378_);
                        v_impl_7527_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_7375_, v_v_7376_, v_r_7382_);
                        v___x_7528_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_7381_) == 0 {
                            v_size_7529_ = lean_ctor_get(v_l_7381_, 0);
                            v_size_7530_ = lean_ctor_get(v_impl_7527_, 0);
                            lean_inc(v_size_7530_);
                            v_k_7531_ = lean_ctor_get(v_impl_7527_, 1);
                            lean_inc(v_k_7531_);
                            v_v_7532_ = lean_ctor_get(v_impl_7527_, 2);
                            lean_inc(v_v_7532_);
                            v_l_7533_ = lean_ctor_get(v_impl_7527_, 3);
                            lean_inc(v_l_7533_);
                            v_r_7534_ = lean_ctor_get(v_impl_7527_, 4);
                            lean_inc(v_r_7534_);
                            v___x_7535_ = lean_unsigned_to_nat(3);
                            v___x_7536_ = lean_nat_mul(v___x_7535_, v_size_7529_);
                            v___x_7537_ = lean_nat_dec_lt(v___x_7536_, v_size_7530_);
                            lean_dec(v___x_7536_);
                            if v___x_7537_ == 0 {
                                lean_dec(v_r_7534_);
                                lean_dec(v_l_7533_);
                                lean_dec(v_v_7532_);
                                lean_dec(v_k_7531_);
                                v___x_7538_ = lean_nat_add(v___x_7528_, v_size_7529_);
                                v___x_7539_ = lean_nat_add(v___x_7538_, v_size_7530_);
                                lean_dec(v_size_7530_);
                                lean_dec(v___x_7538_);
                                if v_isShared_7385_ == 0 {
                                    lean_ctor_set(v___x_7384_, 4, v_impl_7527_);
                                    lean_ctor_set(v___x_7384_, 0, v___x_7539_);
                                    v___x_7541_ = v___x_7384_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7542_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_7542_, 0, v___x_7539_);
                                    lean_ctor_set(v_reuseFailAlloc_7542_, 1, v_k_7379_);
                                    lean_ctor_set(v_reuseFailAlloc_7542_, 2, v_v_7380_);
                                    lean_ctor_set(v_reuseFailAlloc_7542_, 3, v_l_7381_);
                                    lean_ctor_set(v_reuseFailAlloc_7542_, 4, v_impl_7527_);
                                    v___x_7541_ = v_reuseFailAlloc_7542_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_7606_ = (!lean_is_exclusive(v_impl_7527_)) as u8;
                                if v_isSharedCheck_7606_ == 0 {
                                    v_unused_7607_ = lean_ctor_get(v_impl_7527_, 4);
                                    lean_dec(v_unused_7607_);
                                    v_unused_7608_ = lean_ctor_get(v_impl_7527_, 3);
                                    lean_dec(v_unused_7608_);
                                    v_unused_7609_ = lean_ctor_get(v_impl_7527_, 2);
                                    lean_dec(v_unused_7609_);
                                    v_unused_7610_ = lean_ctor_get(v_impl_7527_, 1);
                                    lean_dec(v_unused_7610_);
                                    v_unused_7611_ = lean_ctor_get(v_impl_7527_, 0);
                                    lean_dec(v_unused_7611_);
                                    v___x_7544_ = v_impl_7527_;
                                    v_isShared_7545_ = v_isSharedCheck_7606_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_7527_);
                                    v___x_7544_ = lean_box(0);
                                    v_isShared_7545_ = v_isSharedCheck_7606_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_7612_ = lean_ctor_get(v_impl_7527_, 3);
                            lean_inc(v_l_7612_);
                            if lean_obj_tag(v_l_7612_) == 0 {
                                v_r_7613_ = lean_ctor_get(v_impl_7527_, 4);
                                v_k_7614_ = lean_ctor_get(v_impl_7527_, 1);
                                v_v_7615_ = lean_ctor_get(v_impl_7527_, 2);
                                v_isSharedCheck_7638_ = (!lean_is_exclusive(v_impl_7527_)) as u8;
                                if v_isSharedCheck_7638_ == 0 {
                                    v_unused_7639_ = lean_ctor_get(v_impl_7527_, 3);
                                    lean_dec(v_unused_7639_);
                                    v_unused_7640_ = lean_ctor_get(v_impl_7527_, 0);
                                    lean_dec(v_unused_7640_);
                                    v___x_7617_ = v_impl_7527_;
                                    v_isShared_7618_ = v_isSharedCheck_7638_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_7613_);
                                    lean_inc(v_v_7615_);
                                    lean_inc(v_k_7614_);
                                    lean_dec(v_impl_7527_);
                                    v___x_7617_ = lean_box(0);
                                    v_isShared_7618_ = v_isSharedCheck_7638_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_7641_ = lean_ctor_get(v_impl_7527_, 4);
                                lean_inc(v_r_7641_);
                                if lean_obj_tag(v_r_7641_) == 0 {
                                    v_k_7642_ = lean_ctor_get(v_impl_7527_, 1);
                                    v_v_7643_ = lean_ctor_get(v_impl_7527_, 2);
                                    v_isSharedCheck_7654_ =
                                        (!lean_is_exclusive(v_impl_7527_)) as u8;
                                    if v_isSharedCheck_7654_ == 0 {
                                        v_unused_7655_ = lean_ctor_get(v_impl_7527_, 4);
                                        lean_dec(v_unused_7655_);
                                        v_unused_7656_ = lean_ctor_get(v_impl_7527_, 3);
                                        lean_dec(v_unused_7656_);
                                        v_unused_7657_ = lean_ctor_get(v_impl_7527_, 0);
                                        lean_dec(v_unused_7657_);
                                        v___x_7645_ = v_impl_7527_;
                                        v_isShared_7646_ = v_isSharedCheck_7654_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_7643_);
                                        lean_inc(v_k_7642_);
                                        lean_dec(v_impl_7527_);
                                        v___x_7645_ = lean_box(0);
                                        v_isShared_7646_ = v_isSharedCheck_7654_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_7658_ = lean_unsigned_to_nat(2);
                                    if v_isShared_7385_ == 0 {
                                        lean_ctor_set(v___x_7384_, 4, v_impl_7527_);
                                        lean_ctor_set(v___x_7384_, 3, v_r_7641_);
                                        lean_ctor_set(v___x_7384_, 0, v___x_7658_);
                                        v___x_7660_ = v___x_7384_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7661_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_7661_, 0, v___x_7658_);
                                        lean_ctor_set(v_reuseFailAlloc_7661_, 1, v_k_7379_);
                                        lean_ctor_set(v_reuseFailAlloc_7661_, 2, v_v_7380_);
                                        lean_ctor_set(v_reuseFailAlloc_7661_, 3, v_r_7641_);
                                        lean_ctor_set(v_reuseFailAlloc_7661_, 4, v_impl_7527_);
                                        v___x_7660_ = v_reuseFailAlloc_7661_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_7401_;
            }
            3 => {
                v_size_7406_ = lean_ctor_get(v_l_7393_, 0);
                v_size_7407_ = lean_ctor_get(v_r_7394_, 0);
                v_k_7408_ = lean_ctor_get(v_r_7394_, 1);
                v_v_7409_ = lean_ctor_get(v_r_7394_, 2);
                v_l_7410_ = lean_ctor_get(v_r_7394_, 3);
                v_r_7411_ = lean_ctor_get(v_r_7394_, 4);
                v___x_7412_ = lean_unsigned_to_nat(2);
                v___x_7413_ = lean_nat_mul(v___x_7412_, v_size_7406_);
                v___x_7414_ = lean_nat_dec_lt(v_size_7407_, v___x_7413_);
                lean_dec(v___x_7413_);
                if v___x_7414_ == 0 {
                    lean_inc(v_r_7411_);
                    lean_inc(v_l_7410_);
                    lean_inc(v_v_7409_);
                    lean_inc(v_k_7408_);
                    v_isSharedCheck_7443_ = (!lean_is_exclusive(v_r_7394_)) as u8;
                    if v_isSharedCheck_7443_ == 0 {
                        v_unused_7444_ = lean_ctor_get(v_r_7394_, 4);
                        lean_dec(v_unused_7444_);
                        v_unused_7445_ = lean_ctor_get(v_r_7394_, 3);
                        lean_dec(v_unused_7445_);
                        v_unused_7446_ = lean_ctor_get(v_r_7394_, 2);
                        lean_dec(v_unused_7446_);
                        v_unused_7447_ = lean_ctor_get(v_r_7394_, 1);
                        lean_dec(v_unused_7447_);
                        v_unused_7448_ = lean_ctor_get(v_r_7394_, 0);
                        lean_dec(v_unused_7448_);
                        v___x_7416_ = v_r_7394_;
                        v_isShared_7417_ = v_isSharedCheck_7443_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_7394_);
                        v___x_7416_ = lean_box(0);
                        v_isShared_7417_ = v_isSharedCheck_7443_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7384_);
                    v___x_7449_ = lean_nat_add(v___x_7388_, v_size_7390_);
                    lean_dec(v_size_7390_);
                    v___x_7450_ = lean_nat_add(v___x_7449_, v_size_7389_);
                    lean_dec(v___x_7449_);
                    v___x_7451_ = lean_nat_add(v___x_7388_, v_size_7389_);
                    v___x_7452_ = lean_nat_add(v___x_7451_, v_size_7407_);
                    lean_dec(v___x_7451_);
                    lean_inc_ref(v_r_7382_);
                    if v_isShared_7405_ == 0 {
                        lean_ctor_set(v___x_7404_, 4, v_r_7382_);
                        lean_ctor_set(v___x_7404_, 3, v_r_7394_);
                        lean_ctor_set(v___x_7404_, 2, v_v_7380_);
                        lean_ctor_set(v___x_7404_, 1, v_k_7379_);
                        lean_ctor_set(v___x_7404_, 0, v___x_7452_);
                        v___x_7454_ = v___x_7404_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_7467_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7467_, 0, v___x_7452_);
                        lean_ctor_set(v_reuseFailAlloc_7467_, 1, v_k_7379_);
                        lean_ctor_set(v_reuseFailAlloc_7467_, 2, v_v_7380_);
                        lean_ctor_set(v_reuseFailAlloc_7467_, 3, v_r_7394_);
                        lean_ctor_set(v_reuseFailAlloc_7467_, 4, v_r_7382_);
                        v___x_7454_ = v_reuseFailAlloc_7467_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7418_ = lean_nat_add(v___x_7388_, v_size_7390_);
                lean_dec(v_size_7390_);
                v___x_7419_ = lean_nat_add(v___x_7418_, v_size_7389_);
                lean_dec(v___x_7418_);
                v___x_7431_ = lean_nat_add(v___x_7388_, v_size_7406_);
                if lean_obj_tag(v_l_7410_) == 0 {
                    v_size_7441_ = lean_ctor_get(v_l_7410_, 0);
                    lean_inc(v_size_7441_);
                    v___y_7433_ = v_size_7441_;
                    state = 8;
                    continue;
                } else {
                    v___x_7442_ = lean_unsigned_to_nat(0);
                    v___y_7433_ = v___x_7442_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_7424_ = lean_nat_add(v___y_7422_, v___y_7423_);
                lean_dec(v___y_7423_);
                lean_dec(v___y_7422_);
                if v_isShared_7417_ == 0 {
                    lean_ctor_set(v___x_7416_, 4, v_r_7382_);
                    lean_ctor_set(v___x_7416_, 3, v_r_7411_);
                    lean_ctor_set(v___x_7416_, 2, v_v_7380_);
                    lean_ctor_set(v___x_7416_, 1, v_k_7379_);
                    lean_ctor_set(v___x_7416_, 0, v___x_7424_);
                    v___x_7426_ = v___x_7416_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7430_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7430_, 0, v___x_7424_);
                    lean_ctor_set(v_reuseFailAlloc_7430_, 1, v_k_7379_);
                    lean_ctor_set(v_reuseFailAlloc_7430_, 2, v_v_7380_);
                    lean_ctor_set(v_reuseFailAlloc_7430_, 3, v_r_7411_);
                    lean_ctor_set(v_reuseFailAlloc_7430_, 4, v_r_7382_);
                    v___x_7426_ = v_reuseFailAlloc_7430_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7405_ == 0 {
                    lean_ctor_set(v___x_7404_, 4, v___x_7426_);
                    lean_ctor_set(v___x_7404_, 3, v___y_7421_);
                    lean_ctor_set(v___x_7404_, 2, v_v_7409_);
                    lean_ctor_set(v___x_7404_, 1, v_k_7408_);
                    lean_ctor_set(v___x_7404_, 0, v___x_7419_);
                    v___x_7428_ = v___x_7404_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7429_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7429_, 0, v___x_7419_);
                    lean_ctor_set(v_reuseFailAlloc_7429_, 1, v_k_7408_);
                    lean_ctor_set(v_reuseFailAlloc_7429_, 2, v_v_7409_);
                    lean_ctor_set(v_reuseFailAlloc_7429_, 3, v___y_7421_);
                    lean_ctor_set(v_reuseFailAlloc_7429_, 4, v___x_7426_);
                    v___x_7428_ = v_reuseFailAlloc_7429_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7428_;
            }
            8 => {
                v___x_7434_ = lean_nat_add(v___x_7431_, v___y_7433_);
                lean_dec(v___y_7433_);
                lean_dec(v___x_7431_);
                if v_isShared_7385_ == 0 {
                    lean_ctor_set(v___x_7384_, 4, v_l_7410_);
                    lean_ctor_set(v___x_7384_, 3, v_l_7393_);
                    lean_ctor_set(v___x_7384_, 2, v_v_7392_);
                    lean_ctor_set(v___x_7384_, 1, v_k_7391_);
                    lean_ctor_set(v___x_7384_, 0, v___x_7434_);
                    v___x_7436_ = v___x_7384_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7440_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7440_, 0, v___x_7434_);
                    lean_ctor_set(v_reuseFailAlloc_7440_, 1, v_k_7391_);
                    lean_ctor_set(v_reuseFailAlloc_7440_, 2, v_v_7392_);
                    lean_ctor_set(v_reuseFailAlloc_7440_, 3, v_l_7393_);
                    lean_ctor_set(v_reuseFailAlloc_7440_, 4, v_l_7410_);
                    v___x_7436_ = v_reuseFailAlloc_7440_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7437_ = lean_nat_add(v___x_7388_, v_size_7389_);
                if lean_obj_tag(v_r_7411_) == 0 {
                    v_size_7438_ = lean_ctor_get(v_r_7411_, 0);
                    lean_inc(v_size_7438_);
                    v___y_7421_ = v___x_7436_;
                    v___y_7422_ = v___x_7437_;
                    v___y_7423_ = v_size_7438_;
                    state = 5;
                    continue;
                } else {
                    v___x_7439_ = lean_unsigned_to_nat(0);
                    v___y_7421_ = v___x_7436_;
                    v___y_7422_ = v___x_7437_;
                    v___y_7423_ = v___x_7439_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_7461_ = (!lean_is_exclusive(v_r_7382_)) as u8;
                if v_isSharedCheck_7461_ == 0 {
                    v_unused_7462_ = lean_ctor_get(v_r_7382_, 4);
                    lean_dec(v_unused_7462_);
                    v_unused_7463_ = lean_ctor_get(v_r_7382_, 3);
                    lean_dec(v_unused_7463_);
                    v_unused_7464_ = lean_ctor_get(v_r_7382_, 2);
                    lean_dec(v_unused_7464_);
                    v_unused_7465_ = lean_ctor_get(v_r_7382_, 1);
                    lean_dec(v_unused_7465_);
                    v_unused_7466_ = lean_ctor_get(v_r_7382_, 0);
                    lean_dec(v_unused_7466_);
                    v___x_7456_ = v_r_7382_;
                    v_isShared_7457_ = v_isSharedCheck_7461_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_7382_);
                    v___x_7456_ = lean_box(0);
                    v_isShared_7457_ = v_isSharedCheck_7461_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_7457_ == 0 {
                    lean_ctor_set(v___x_7456_, 4, v___x_7454_);
                    lean_ctor_set(v___x_7456_, 3, v_l_7393_);
                    lean_ctor_set(v___x_7456_, 2, v_v_7392_);
                    lean_ctor_set(v___x_7456_, 1, v_k_7391_);
                    lean_ctor_set(v___x_7456_, 0, v___x_7450_);
                    v___x_7459_ = v___x_7456_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7460_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7460_, 0, v___x_7450_);
                    lean_ctor_set(v_reuseFailAlloc_7460_, 1, v_k_7391_);
                    lean_ctor_set(v_reuseFailAlloc_7460_, 2, v_v_7392_);
                    lean_ctor_set(v_reuseFailAlloc_7460_, 3, v_l_7393_);
                    lean_ctor_set(v_reuseFailAlloc_7460_, 4, v___x_7454_);
                    v___x_7459_ = v_reuseFailAlloc_7460_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7459_;
            }
            13 => {
                v___x_7481_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_7475_);
                if v_isShared_7480_ == 0 {
                    lean_ctor_set(v___x_7479_, 3, v_r_7475_);
                    lean_ctor_set(v___x_7479_, 2, v_v_7380_);
                    lean_ctor_set(v___x_7479_, 1, v_k_7379_);
                    lean_ctor_set(v___x_7479_, 0, v___x_7388_);
                    v___x_7483_ = v___x_7479_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7487_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7487_, 0, v___x_7388_);
                    lean_ctor_set(v_reuseFailAlloc_7487_, 1, v_k_7379_);
                    lean_ctor_set(v_reuseFailAlloc_7487_, 2, v_v_7380_);
                    lean_ctor_set(v_reuseFailAlloc_7487_, 3, v_r_7475_);
                    lean_ctor_set(v_reuseFailAlloc_7487_, 4, v_r_7475_);
                    v___x_7483_ = v_reuseFailAlloc_7487_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_7385_ == 0 {
                    lean_ctor_set(v___x_7384_, 4, v___x_7483_);
                    lean_ctor_set(v___x_7384_, 3, v_l_7474_);
                    lean_ctor_set(v___x_7384_, 2, v_v_7477_);
                    lean_ctor_set(v___x_7384_, 1, v_k_7476_);
                    lean_ctor_set(v___x_7384_, 0, v___x_7481_);
                    v___x_7485_ = v___x_7384_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7486_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7486_, 0, v___x_7481_);
                    lean_ctor_set(v_reuseFailAlloc_7486_, 1, v_k_7476_);
                    lean_ctor_set(v_reuseFailAlloc_7486_, 2, v_v_7477_);
                    lean_ctor_set(v_reuseFailAlloc_7486_, 3, v_l_7474_);
                    lean_ctor_set(v_reuseFailAlloc_7486_, 4, v___x_7483_);
                    v___x_7485_ = v_reuseFailAlloc_7486_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7485_;
            }
            16 => {
                v_k_7497_ = lean_ctor_get(v_r_7491_, 1);
                v_v_7498_ = lean_ctor_get(v_r_7491_, 2);
                v_isSharedCheck_7512_ = (!lean_is_exclusive(v_r_7491_)) as u8;
                if v_isSharedCheck_7512_ == 0 {
                    v_unused_7513_ = lean_ctor_get(v_r_7491_, 4);
                    lean_dec(v_unused_7513_);
                    v_unused_7514_ = lean_ctor_get(v_r_7491_, 3);
                    lean_dec(v_unused_7514_);
                    v_unused_7515_ = lean_ctor_get(v_r_7491_, 0);
                    lean_dec(v_unused_7515_);
                    v___x_7500_ = v_r_7491_;
                    v_isShared_7501_ = v_isSharedCheck_7512_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_7498_);
                    lean_inc(v_k_7497_);
                    lean_dec(v_r_7491_);
                    v___x_7500_ = lean_box(0);
                    v_isShared_7501_ = v_isSharedCheck_7512_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_7502_ = lean_unsigned_to_nat(3);
                if v_isShared_7501_ == 0 {
                    lean_ctor_set(v___x_7500_, 4, v_l_7474_);
                    lean_ctor_set(v___x_7500_, 3, v_l_7474_);
                    lean_ctor_set(v___x_7500_, 2, v_v_7493_);
                    lean_ctor_set(v___x_7500_, 1, v_k_7492_);
                    lean_ctor_set(v___x_7500_, 0, v___x_7388_);
                    v___x_7504_ = v___x_7500_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7511_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7511_, 0, v___x_7388_);
                    lean_ctor_set(v_reuseFailAlloc_7511_, 1, v_k_7492_);
                    lean_ctor_set(v_reuseFailAlloc_7511_, 2, v_v_7493_);
                    lean_ctor_set(v_reuseFailAlloc_7511_, 3, v_l_7474_);
                    lean_ctor_set(v_reuseFailAlloc_7511_, 4, v_l_7474_);
                    v___x_7504_ = v_reuseFailAlloc_7511_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_7496_ == 0 {
                    lean_ctor_set(v___x_7495_, 4, v_l_7474_);
                    lean_ctor_set(v___x_7495_, 2, v_v_7380_);
                    lean_ctor_set(v___x_7495_, 1, v_k_7379_);
                    lean_ctor_set(v___x_7495_, 0, v___x_7388_);
                    v___x_7506_ = v___x_7495_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7510_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7510_, 0, v___x_7388_);
                    lean_ctor_set(v_reuseFailAlloc_7510_, 1, v_k_7379_);
                    lean_ctor_set(v_reuseFailAlloc_7510_, 2, v_v_7380_);
                    lean_ctor_set(v_reuseFailAlloc_7510_, 3, v_l_7474_);
                    lean_ctor_set(v_reuseFailAlloc_7510_, 4, v_l_7474_);
                    v___x_7506_ = v_reuseFailAlloc_7510_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_7385_ == 0 {
                    lean_ctor_set(v___x_7384_, 4, v___x_7506_);
                    lean_ctor_set(v___x_7384_, 3, v___x_7504_);
                    lean_ctor_set(v___x_7384_, 2, v_v_7498_);
                    lean_ctor_set(v___x_7384_, 1, v_k_7497_);
                    lean_ctor_set(v___x_7384_, 0, v___x_7502_);
                    v___x_7508_ = v___x_7384_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7509_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7509_, 0, v___x_7502_);
                    lean_ctor_set(v_reuseFailAlloc_7509_, 1, v_k_7497_);
                    lean_ctor_set(v_reuseFailAlloc_7509_, 2, v_v_7498_);
                    lean_ctor_set(v_reuseFailAlloc_7509_, 3, v___x_7504_);
                    lean_ctor_set(v_reuseFailAlloc_7509_, 4, v___x_7506_);
                    v___x_7508_ = v_reuseFailAlloc_7509_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7508_;
            }
            21 => {
                return v___x_7522_;
            }
            22 => {
                return v___x_7525_;
            }
            23 => {
                return v___x_7541_;
            }
            24 => {
                v_size_7546_ = lean_ctor_get(v_l_7533_, 0);
                v_k_7547_ = lean_ctor_get(v_l_7533_, 1);
                v_v_7548_ = lean_ctor_get(v_l_7533_, 2);
                v_l_7549_ = lean_ctor_get(v_l_7533_, 3);
                v_r_7550_ = lean_ctor_get(v_l_7533_, 4);
                v_size_7551_ = lean_ctor_get(v_r_7534_, 0);
                v___x_7552_ = lean_unsigned_to_nat(2);
                v___x_7553_ = lean_nat_mul(v___x_7552_, v_size_7551_);
                v___x_7554_ = lean_nat_dec_lt(v_size_7546_, v___x_7553_);
                lean_dec(v___x_7553_);
                if v___x_7554_ == 0 {
                    lean_inc(v_r_7550_);
                    lean_inc(v_l_7549_);
                    lean_inc(v_v_7548_);
                    lean_inc(v_k_7547_);
                    v_isSharedCheck_7582_ = (!lean_is_exclusive(v_l_7533_)) as u8;
                    if v_isSharedCheck_7582_ == 0 {
                        v_unused_7583_ = lean_ctor_get(v_l_7533_, 4);
                        lean_dec(v_unused_7583_);
                        v_unused_7584_ = lean_ctor_get(v_l_7533_, 3);
                        lean_dec(v_unused_7584_);
                        v_unused_7585_ = lean_ctor_get(v_l_7533_, 2);
                        lean_dec(v_unused_7585_);
                        v_unused_7586_ = lean_ctor_get(v_l_7533_, 1);
                        lean_dec(v_unused_7586_);
                        v_unused_7587_ = lean_ctor_get(v_l_7533_, 0);
                        lean_dec(v_unused_7587_);
                        v___x_7556_ = v_l_7533_;
                        v_isShared_7557_ = v_isSharedCheck_7582_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_7533_);
                        v___x_7556_ = lean_box(0);
                        v_isShared_7557_ = v_isSharedCheck_7582_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7384_);
                    v___x_7588_ = lean_nat_add(v___x_7528_, v_size_7529_);
                    v___x_7589_ = lean_nat_add(v___x_7588_, v_size_7530_);
                    lean_dec(v_size_7530_);
                    v___x_7590_ = lean_nat_add(v___x_7588_, v_size_7546_);
                    lean_dec(v___x_7588_);
                    lean_inc_ref(v_l_7381_);
                    if v_isShared_7545_ == 0 {
                        lean_ctor_set(v___x_7544_, 4, v_l_7533_);
                        lean_ctor_set(v___x_7544_, 3, v_l_7381_);
                        lean_ctor_set(v___x_7544_, 2, v_v_7380_);
                        lean_ctor_set(v___x_7544_, 1, v_k_7379_);
                        lean_ctor_set(v___x_7544_, 0, v___x_7590_);
                        v___x_7592_ = v___x_7544_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_7605_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7605_, 0, v___x_7590_);
                        lean_ctor_set(v_reuseFailAlloc_7605_, 1, v_k_7379_);
                        lean_ctor_set(v_reuseFailAlloc_7605_, 2, v_v_7380_);
                        lean_ctor_set(v_reuseFailAlloc_7605_, 3, v_l_7381_);
                        lean_ctor_set(v_reuseFailAlloc_7605_, 4, v_l_7533_);
                        v___x_7592_ = v_reuseFailAlloc_7605_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_7558_ = lean_nat_add(v___x_7528_, v_size_7529_);
                v___x_7559_ = lean_nat_add(v___x_7558_, v_size_7530_);
                lean_dec(v_size_7530_);
                if lean_obj_tag(v_l_7549_) == 0 {
                    v_size_7580_ = lean_ctor_get(v_l_7549_, 0);
                    lean_inc(v_size_7580_);
                    v___y_7572_ = v_size_7580_;
                    state = 29;
                    continue;
                } else {
                    v___x_7581_ = lean_unsigned_to_nat(0);
                    v___y_7572_ = v___x_7581_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_7564_ = lean_nat_add(v___y_7562_, v___y_7563_);
                lean_dec(v___y_7563_);
                lean_dec(v___y_7562_);
                if v_isShared_7557_ == 0 {
                    lean_ctor_set(v___x_7556_, 4, v_r_7534_);
                    lean_ctor_set(v___x_7556_, 3, v_r_7550_);
                    lean_ctor_set(v___x_7556_, 2, v_v_7532_);
                    lean_ctor_set(v___x_7556_, 1, v_k_7531_);
                    lean_ctor_set(v___x_7556_, 0, v___x_7564_);
                    v___x_7566_ = v___x_7556_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_7570_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7570_, 0, v___x_7564_);
                    lean_ctor_set(v_reuseFailAlloc_7570_, 1, v_k_7531_);
                    lean_ctor_set(v_reuseFailAlloc_7570_, 2, v_v_7532_);
                    lean_ctor_set(v_reuseFailAlloc_7570_, 3, v_r_7550_);
                    lean_ctor_set(v_reuseFailAlloc_7570_, 4, v_r_7534_);
                    v___x_7566_ = v_reuseFailAlloc_7570_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_7545_ == 0 {
                    lean_ctor_set(v___x_7544_, 4, v___x_7566_);
                    lean_ctor_set(v___x_7544_, 3, v___y_7561_);
                    lean_ctor_set(v___x_7544_, 2, v_v_7548_);
                    lean_ctor_set(v___x_7544_, 1, v_k_7547_);
                    lean_ctor_set(v___x_7544_, 0, v___x_7559_);
                    v___x_7568_ = v___x_7544_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_7569_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7569_, 0, v___x_7559_);
                    lean_ctor_set(v_reuseFailAlloc_7569_, 1, v_k_7547_);
                    lean_ctor_set(v_reuseFailAlloc_7569_, 2, v_v_7548_);
                    lean_ctor_set(v_reuseFailAlloc_7569_, 3, v___y_7561_);
                    lean_ctor_set(v_reuseFailAlloc_7569_, 4, v___x_7566_);
                    v___x_7568_ = v_reuseFailAlloc_7569_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_7568_;
            }
            29 => {
                v___x_7573_ = lean_nat_add(v___x_7558_, v___y_7572_);
                lean_dec(v___y_7572_);
                lean_dec(v___x_7558_);
                if v_isShared_7385_ == 0 {
                    lean_ctor_set(v___x_7384_, 4, v_l_7549_);
                    lean_ctor_set(v___x_7384_, 0, v___x_7573_);
                    v___x_7575_ = v___x_7384_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_7579_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7579_, 0, v___x_7573_);
                    lean_ctor_set(v_reuseFailAlloc_7579_, 1, v_k_7379_);
                    lean_ctor_set(v_reuseFailAlloc_7579_, 2, v_v_7380_);
                    lean_ctor_set(v_reuseFailAlloc_7579_, 3, v_l_7381_);
                    lean_ctor_set(v_reuseFailAlloc_7579_, 4, v_l_7549_);
                    v___x_7575_ = v_reuseFailAlloc_7579_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_7576_ = lean_nat_add(v___x_7528_, v_size_7551_);
                if lean_obj_tag(v_r_7550_) == 0 {
                    v_size_7577_ = lean_ctor_get(v_r_7550_, 0);
                    lean_inc(v_size_7577_);
                    v___y_7561_ = v___x_7575_;
                    v___y_7562_ = v___x_7576_;
                    v___y_7563_ = v_size_7577_;
                    state = 26;
                    continue;
                } else {
                    v___x_7578_ = lean_unsigned_to_nat(0);
                    v___y_7561_ = v___x_7575_;
                    v___y_7562_ = v___x_7576_;
                    v___y_7563_ = v___x_7578_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_7599_ = (!lean_is_exclusive(v_l_7381_)) as u8;
                if v_isSharedCheck_7599_ == 0 {
                    v_unused_7600_ = lean_ctor_get(v_l_7381_, 4);
                    lean_dec(v_unused_7600_);
                    v_unused_7601_ = lean_ctor_get(v_l_7381_, 3);
                    lean_dec(v_unused_7601_);
                    v_unused_7602_ = lean_ctor_get(v_l_7381_, 2);
                    lean_dec(v_unused_7602_);
                    v_unused_7603_ = lean_ctor_get(v_l_7381_, 1);
                    lean_dec(v_unused_7603_);
                    v_unused_7604_ = lean_ctor_get(v_l_7381_, 0);
                    lean_dec(v_unused_7604_);
                    v___x_7594_ = v_l_7381_;
                    v_isShared_7595_ = v_isSharedCheck_7599_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_7381_);
                    v___x_7594_ = lean_box(0);
                    v_isShared_7595_ = v_isSharedCheck_7599_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_7595_ == 0 {
                    lean_ctor_set(v___x_7594_, 4, v_r_7534_);
                    lean_ctor_set(v___x_7594_, 3, v___x_7592_);
                    lean_ctor_set(v___x_7594_, 2, v_v_7532_);
                    lean_ctor_set(v___x_7594_, 1, v_k_7531_);
                    lean_ctor_set(v___x_7594_, 0, v___x_7589_);
                    v___x_7597_ = v___x_7594_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_7598_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7598_, 0, v___x_7589_);
                    lean_ctor_set(v_reuseFailAlloc_7598_, 1, v_k_7531_);
                    lean_ctor_set(v_reuseFailAlloc_7598_, 2, v_v_7532_);
                    lean_ctor_set(v_reuseFailAlloc_7598_, 3, v___x_7592_);
                    lean_ctor_set(v_reuseFailAlloc_7598_, 4, v_r_7534_);
                    v___x_7597_ = v_reuseFailAlloc_7598_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_7597_;
            }
            34 => {
                v_k_7619_ = lean_ctor_get(v_l_7612_, 1);
                v_v_7620_ = lean_ctor_get(v_l_7612_, 2);
                v_isSharedCheck_7634_ = (!lean_is_exclusive(v_l_7612_)) as u8;
                if v_isSharedCheck_7634_ == 0 {
                    v_unused_7635_ = lean_ctor_get(v_l_7612_, 4);
                    lean_dec(v_unused_7635_);
                    v_unused_7636_ = lean_ctor_get(v_l_7612_, 3);
                    lean_dec(v_unused_7636_);
                    v_unused_7637_ = lean_ctor_get(v_l_7612_, 0);
                    lean_dec(v_unused_7637_);
                    v___x_7622_ = v_l_7612_;
                    v_isShared_7623_ = v_isSharedCheck_7634_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_7620_);
                    lean_inc(v_k_7619_);
                    lean_dec(v_l_7612_);
                    v___x_7622_ = lean_box(0);
                    v_isShared_7623_ = v_isSharedCheck_7634_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_7624_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_7613_, 2);
                if v_isShared_7623_ == 0 {
                    lean_ctor_set(v___x_7622_, 4, v_r_7613_);
                    lean_ctor_set(v___x_7622_, 3, v_r_7613_);
                    lean_ctor_set(v___x_7622_, 2, v_v_7380_);
                    lean_ctor_set(v___x_7622_, 1, v_k_7379_);
                    lean_ctor_set(v___x_7622_, 0, v___x_7528_);
                    v___x_7626_ = v___x_7622_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_7633_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7633_, 0, v___x_7528_);
                    lean_ctor_set(v_reuseFailAlloc_7633_, 1, v_k_7379_);
                    lean_ctor_set(v_reuseFailAlloc_7633_, 2, v_v_7380_);
                    lean_ctor_set(v_reuseFailAlloc_7633_, 3, v_r_7613_);
                    lean_ctor_set(v_reuseFailAlloc_7633_, 4, v_r_7613_);
                    v___x_7626_ = v_reuseFailAlloc_7633_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_7613_);
                if v_isShared_7618_ == 0 {
                    lean_ctor_set(v___x_7617_, 3, v_r_7613_);
                    lean_ctor_set(v___x_7617_, 0, v___x_7528_);
                    v___x_7628_ = v___x_7617_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_7632_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7632_, 0, v___x_7528_);
                    lean_ctor_set(v_reuseFailAlloc_7632_, 1, v_k_7614_);
                    lean_ctor_set(v_reuseFailAlloc_7632_, 2, v_v_7615_);
                    lean_ctor_set(v_reuseFailAlloc_7632_, 3, v_r_7613_);
                    lean_ctor_set(v_reuseFailAlloc_7632_, 4, v_r_7613_);
                    v___x_7628_ = v_reuseFailAlloc_7632_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_7385_ == 0 {
                    lean_ctor_set(v___x_7384_, 4, v___x_7628_);
                    lean_ctor_set(v___x_7384_, 3, v___x_7626_);
                    lean_ctor_set(v___x_7384_, 2, v_v_7620_);
                    lean_ctor_set(v___x_7384_, 1, v_k_7619_);
                    lean_ctor_set(v___x_7384_, 0, v___x_7624_);
                    v___x_7630_ = v___x_7384_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_7631_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7631_, 0, v___x_7624_);
                    lean_ctor_set(v_reuseFailAlloc_7631_, 1, v_k_7619_);
                    lean_ctor_set(v_reuseFailAlloc_7631_, 2, v_v_7620_);
                    lean_ctor_set(v_reuseFailAlloc_7631_, 3, v___x_7626_);
                    lean_ctor_set(v_reuseFailAlloc_7631_, 4, v___x_7628_);
                    v___x_7630_ = v_reuseFailAlloc_7631_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_7630_;
            }
            39 => {
                v___x_7647_ = lean_unsigned_to_nat(3);
                if v_isShared_7646_ == 0 {
                    lean_ctor_set(v___x_7645_, 4, v_l_7612_);
                    lean_ctor_set(v___x_7645_, 2, v_v_7380_);
                    lean_ctor_set(v___x_7645_, 1, v_k_7379_);
                    lean_ctor_set(v___x_7645_, 0, v___x_7528_);
                    v___x_7649_ = v___x_7645_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_7653_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 0, v___x_7528_);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 1, v_k_7379_);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 2, v_v_7380_);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 3, v_l_7612_);
                    lean_ctor_set(v_reuseFailAlloc_7653_, 4, v_l_7612_);
                    v___x_7649_ = v_reuseFailAlloc_7653_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_7385_ == 0 {
                    lean_ctor_set(v___x_7384_, 4, v_r_7641_);
                    lean_ctor_set(v___x_7384_, 3, v___x_7649_);
                    lean_ctor_set(v___x_7384_, 2, v_v_7643_);
                    lean_ctor_set(v___x_7384_, 1, v_k_7642_);
                    lean_ctor_set(v___x_7384_, 0, v___x_7647_);
                    v___x_7651_ = v___x_7384_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_7652_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7652_, 0, v___x_7647_);
                    lean_ctor_set(v_reuseFailAlloc_7652_, 1, v_k_7642_);
                    lean_ctor_set(v_reuseFailAlloc_7652_, 2, v_v_7643_);
                    lean_ctor_set(v_reuseFailAlloc_7652_, 3, v___x_7649_);
                    lean_ctor_set(v_reuseFailAlloc_7652_, 4, v_r_7641_);
                    v___x_7651_ = v_reuseFailAlloc_7652_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_7651_;
            }
            42 => {
                return v___x_7660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_LeanLib_initFacetConfigs___closed__0() -> *mut LeanObject {
    let mut v___x_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut LeanObject = core::ptr::null_mut();
    v___x_7665_ = lean_box(1);
    v___x_7666_ = l_Lake_LeanLib_defaultFacetConfig;
    v___x_7667_ = l_Lake_LeanLib_defaultFacet;
    v___x_7668_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
            v___x_7667_,
            v___x_7666_,
            v___x_7665_,
        );
    return v___x_7668_;
}
pub unsafe fn _init_l_Lake_LeanLib_initFacetConfigs___closed__1() -> *mut LeanObject {
    let mut v___x_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut LeanObject = core::ptr::null_mut();
    v___x_7669_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__0_once),
        _init_l_Lake_LeanLib_initFacetConfigs___closed__0,
    );
    v___x_7670_ = l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig;
    v___x_7671_ = l_Lake_LeanLib_modulesFacet;
    v___x_7672_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
            v___x_7671_,
            v___x_7670_,
            v___x_7669_,
        );
    return v___x_7672_;
}
pub unsafe fn _init_l_Lake_LeanLib_initFacetConfigs___closed__2() -> *mut LeanObject {
    let mut v___x_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7676_: *mut LeanObject = core::ptr::null_mut();
    v___x_7673_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__1_once),
        _init_l_Lake_LeanLib_initFacetConfigs___closed__1,
    );
    v___x_7674_ = l_Lake_LeanLib_leanArtsFacetConfig;
    v___x_7675_ = l_Lake_LeanLib_leanArtsFacet;
    v___x_7676_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
            v___x_7675_,
            v___x_7674_,
            v___x_7673_,
        );
    return v___x_7676_;
}
pub unsafe fn _init_l_Lake_LeanLib_initFacetConfigs___closed__3() -> *mut LeanObject {
    let mut v___x_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    v___x_7677_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__2_once),
        _init_l_Lake_LeanLib_initFacetConfigs___closed__2,
    );
    v___x_7678_ = l_Lake_LeanLib_staticFacetConfig;
    v___x_7679_ = l_Lake_LeanLib_staticFacet;
    v___x_7680_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
            v___x_7679_,
            v___x_7678_,
            v___x_7677_,
        );
    return v___x_7680_;
}
pub unsafe fn _init_l_Lake_LeanLib_initFacetConfigs___closed__4() -> *mut LeanObject {
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    v___x_7681_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__3),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__3_once),
        _init_l_Lake_LeanLib_initFacetConfigs___closed__3,
    );
    v___x_7682_ = l_Lake_LeanLib_staticExportFacetConfig;
    v___x_7683_ = l_Lake_LeanLib_staticExportFacet;
    v___x_7684_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
            v___x_7683_,
            v___x_7682_,
            v___x_7681_,
        );
    return v___x_7684_;
}
pub unsafe fn _init_l_Lake_LeanLib_initFacetConfigs___closed__5() -> *mut LeanObject {
    let mut v___x_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    v___x_7685_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__4),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__4_once),
        _init_l_Lake_LeanLib_initFacetConfigs___closed__4,
    );
    v___x_7686_ = l_Lake_LeanLib_sharedFacetConfig;
    v___x_7687_ = l_Lake_LeanLib_sharedFacet;
    v___x_7688_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
            v___x_7687_,
            v___x_7686_,
            v___x_7685_,
        );
    return v___x_7688_;
}
pub unsafe fn _init_l_Lake_LeanLib_initFacetConfigs___closed__6() -> *mut LeanObject {
    let mut v___x_7689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7692_: *mut LeanObject = core::ptr::null_mut();
    v___x_7689_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__5),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__5_once),
        _init_l_Lake_LeanLib_initFacetConfigs___closed__5,
    );
    v___x_7690_ = l_Lake_LeanLib_extraDepFacetConfig;
    v___x_7691_ = l_Lake_LeanLib_extraDepFacet;
    v___x_7692_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
            v___x_7691_,
            v___x_7690_,
            v___x_7689_,
        );
    return v___x_7692_;
}
pub unsafe fn _init_l_Lake_LeanLib_initFacetConfigs() -> *mut LeanObject {
    let mut v___x_7693_: *mut LeanObject = core::ptr::null_mut();
    v___x_7693_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__6),
        core::ptr::addr_of_mut!(l_Lake_LeanLib_initFacetConfigs___closed__6_once),
        _init_l_Lake_LeanLib_initFacetConfigs___closed__6,
    );
    return v___x_7693_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(
    mut v_00_u03b2_7694_: *mut LeanObject,
    mut v_k_7695_: *mut LeanObject,
    mut v_v_7696_: *mut LeanObject,
    mut v_t_7697_: *mut LeanObject,
    mut v_hl_7698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    v___x_7699_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(
            v_k_7695_, v_v_7696_, v_t_7697_,
        );
    return v___x_7699_;
}
pub unsafe fn _init_l_Lake_initLibraryFacetConfigs() -> *mut LeanObject {
    let mut v___x_7700_: *mut LeanObject = core::ptr::null_mut();
    v___x_7700_ = l_Lake_LeanLib_initFacetConfigs;
    return v___x_7700_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Library(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_FacetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Common(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Targets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Register(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Target_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Proc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_LeanLib_leanArtsFacetConfig = _init_l_Lake_LeanLib_leanArtsFacetConfig();
    lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig);
    l_Lake_LeanLib_staticFacetConfig = _init_l_Lake_LeanLib_staticFacetConfig();
    lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig);
    l_Lake_LeanLib_staticExportFacetConfig = _init_l_Lake_LeanLib_staticExportFacetConfig();
    lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig);
    l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5 = _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5();
    lean_mark_persistent(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5);
    l_Lake_LeanLib_sharedFacetConfig = _init_l_Lake_LeanLib_sharedFacetConfig();
    lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig);
    l_Lake_LeanLib_extraDepFacetConfig = _init_l_Lake_LeanLib_extraDepFacetConfig();
    lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig);
    l_Lake_LeanLib_defaultFacetConfig = _init_l_Lake_LeanLib_defaultFacetConfig();
    lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig);
    l_Lake_LeanLib_initFacetConfigs = _init_l_Lake_LeanLib_initFacetConfigs();
    lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs);
    l_Lake_initLibraryFacetConfigs = _init_l_Lake_initLibraryFacetConfigs();
    lean_mark_persistent(l_Lake_initLibraryFacetConfigs);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Library(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Library(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_FacetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Common(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Targets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Register(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Target_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Proc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Library(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Library(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Library(builtin);
}
