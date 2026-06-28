// Lean compiler output
// Module: Lake.Build.Package
// Imports: Lake.Config.FacetConfig Lake.Build.Job.Monad Lake.Build.Infos Lake.Util.Git Lake.Util.Url Lake.Build.Common Lake.Build.Targets Lake.Build.Job.Register Lake.Reservoir
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_Pos_prevn;
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringBool___lam__0___boxed;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::l_Array_extract___redArg;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_normalize,
};
use crate::r#gen::Init::System::IO::{l_IO_FS_instOrdSystemTime_ord, l_System_FilePath_pathExists};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lake::Build::Actions::{l_Lake_download, l_Lake_untar};
use crate::r#gen::Lake::Build::Common::{
    initialize_Lake_Build_Common, l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore,
    l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay,
    l_Lake_BuildMetadata_writeFile, l_Lake_instDecidableEqOutputStatus, l_Lake_readTraceFile,
    runtime_initialize_Lake_Build_Common,
};
use crate::r#gen::Lake::Build::Data::{l_Lake_instDataKindBool, l_Lake_instDataKindUnit};
use crate::r#gen::Lake::Build::Facets::{
    l_Lake_Package_buildCacheFacet, l_Lake_Package_extraDepFacet,
    l_Lake_Package_gitHubReleaseFacet, l_Lake_Package_optBuildCacheFacet,
    l_Lake_Package_optGitHubReleaseFacet, l_Lake_Package_optReservoirBarrelFacet,
    l_Lake_Package_reservoirBarrelFacet,
};
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, l_Lake_Package_depsFacet, l_Lake_Package_transDepsFacet,
    runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Job::Basic::{l_Lake_Job_toOpaque___redArg, l_Lake_JobAction_merge};
use crate::r#gen::Lake::Build::Job::Monad::{
    initialize_Lake_Build_Job_Monad, l_Lake_FetchM_runJobM___boxed, l_Lake_Job_add___redArg,
    l_Lake_Job_async___boxed, l_Lake_Job_async___redArg, l_Lake_Job_await___redArg,
    l_Lake_Job_bindM___redArg, l_Lake_Job_mapM___redArg, l_Lake_Job_mix___redArg,
    l_Lake_JobM_runSpawnM___boxed, runtime_initialize_Lake_Build_Job_Monad,
};
use crate::r#gen::Lake::Build::Job::Register::{
    initialize_Lake_Build_Job_Register, l_Lake_Job_renew___redArg, l_Lake_ensureJob___redArg,
    runtime_initialize_Lake_Build_Job_Register,
};
use crate::r#gen::Lake::Build::Targets::{
    initialize_Lake_Build_Targets, l_Lake_Package_fetchTargetJob,
    runtime_initialize_Lake_Build_Targets,
};
use crate::r#gen::Lake::Build::Trace::{l_Lake_BuildTrace_nil, l_Lake_Hash_nil};
use crate::r#gen::Lake::Config::Defaults::l_Lake_defaultLakeDir;
use crate::r#gen::Lake::Config::FacetConfig::{
    initialize_Lake_Config_FacetConfig, runtime_initialize_Lake_Config_FacetConfig,
};
use crate::r#gen::Lake::Config::Kinds::l_Lake_Package_keyword;
use crate::r#gen::Lake::Config::OutFormat::{
    l_Lake_formatQuery___boxed, l_Lake_instQueryJsonUnit___lam__0,
    l_Lake_instQueryTextUnit___lam__0,
};
use crate::r#gen::Lake::Reservoir::{
    initialize_Lake_Reservoir, l_Lake_Reservoir_pkgApiUrl, runtime_initialize_Lake_Reservoir,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lake::Util::Git::{
    initialize_Lake_Util_Git, l_Lake_Git_defaultRemote, l_Lake_GitRepo_findTag_x3f,
    l_Lake_GitRepo_getFilteredRemoteUrl_x3f, l_Lake_GitRepo_resolveRevision_x3f,
    runtime_initialize_Lake_Util_Git,
};
use crate::r#gen::Lake::Util::IO::l_Lake_removeFileIfExists;
use crate::r#gen::Lake::Util::Log::l_Lake_instDecidableEqVerbosity;
use crate::r#gen::Lake::Util::Name::l_Lake_Name_eraseHead;
use crate::r#gen::Lake::Util::Reservoir::l_Lake_Reservoir_lakeHeaders;
use crate::r#gen::Lake::Util::Url::{
    initialize_Lake_Util_Url, l_Lake_uriEncode, runtime_initialize_Lake_Util_Url,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Lean_instToJsonBool___lam__0___boxed;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::lean_imports_rs::Init::Core::lean_task_pure;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
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
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_string_dec_eq, lean_string_hash, lean_string_utf8_byte_size,
    lean_uint64_dec_eq, lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{lean_io_metadata, lean_io_mono_ms_now};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_7, lean_apply_8, lean_apply_9, lean_box, lean_box_uint64, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint32, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_uint64, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 110, 105, 108, 62, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__2_value
) as *mut LeanObject;
static mut l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_Package_depsFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_depsFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacetConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_Package_depsFacetConfig___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_depsFacetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacetConfig___closed__1_value) as *mut LeanObject;
static mut l_Lake_Package_depsFacetConfig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_depsFacetConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Package_depsFacetConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2_value) as *mut LeanObject;
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lake_Package_transDepsFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_transDepsFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacetConfig___closed__0_value) as *mut LeanObject;
static mut l_Lake_Package_transDepsFacetConfig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_transDepsFacetConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Package_transDepsFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Lake_Package_optBuildCacheFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_optBuildCacheFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacetConfig___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Package_optBuildCacheFacetConfig___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_optBuildCacheFacetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacetConfig___closed__1_value)
        as *mut LeanObject;
static mut l_Lake_Package_optBuildCacheFacetConfig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_optBuildCacheFacetConfig___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Package_optBuildCacheFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 0],
};
static mut l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1_value:
    LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 45, 99, 111, 109, 109, 117, 110, 105, 116,
        121, 0,
    ],
};
static mut l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [32, 40, 114, 117, 110, 32, 119, 105, 116, 104, 32, 39, 45, 118, 39, 32, 102, 111, 114, 32, 100, 101, 116, 97, 105, 108, 115, 41, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 40, 115, 101, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [39, 32, 102, 111, 114, 32, 100, 101, 116, 97, 105, 108, 115, 41, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [98, 117, 105, 108, 100, 105, 110, 103, 32, 102, 114, 111, 109, 32, 115, 111, 117, 114, 99, 101, 59, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 101, 116, 99, 104, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 98, 117, 105, 108, 100, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [98, 117, 105, 108, 100, 105, 110, 103, 32, 102, 114, 111, 109, 32, 115, 111, 117, 114, 99, 101, 59, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 101, 116, 99, 104, 32, 71, 105, 116, 72, 117, 98, 32, 114, 101, 108, 101, 97, 115, 101, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [58, 101, 120, 116, 114, 97, 68, 101, 112, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1_value
) as *mut LeanObject;
static mut l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Package_extraDepFacetConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Package_extraDepFacetConfig___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_extraDepFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_extraDepFacetConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_Package_extraDepFacetConfig___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_extraDepFacetConfig___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_extraDepFacetConfig___closed__1_value) as *mut LeanObject;
static mut l_Lake_Package_extraDepFacetConfig___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_extraDepFacetConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Package_extraDepFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 69, 65, 68, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [47, 98, 97, 114, 114, 101, 108, 63, 114, 101, 118, 61, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [38, 116, 111, 111, 108, 99, 104, 97, 105, 110, 61, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3_value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [76, 101, 97, 110, 32, 116, 111, 111, 108, 99, 104, 97, 105, 110, 32, 110, 111, 116, 32, 107, 110, 111, 119, 110, 59, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 111, 110, 108, 121, 32, 104, 111, 115, 116, 115, 32, 98, 117, 105, 108, 100, 115, 32, 102, 111, 114, 32, 107, 110, 111, 119, 110, 32, 116, 111, 111, 108, 99, 104, 97, 105, 110, 115, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3_value) as *mut LeanObject,3 as *mut LeanObject] };
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 115, 111, 108, 118, 101, 32, 72, 69, 65, 68, 32, 114, 101, 118, 105, 115, 105, 111, 110, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5_value) as *mut LeanObject,3 as *mut LeanObject] };
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [112, 97, 99, 107, 97, 103, 101, 32, 104, 97, 115, 32, 110, 111, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 32, 115, 99, 111, 112, 101, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7_value) as *mut LeanObject,3 as *mut LeanObject] };
static mut l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [110, 111, 32, 114, 101, 108, 101, 97, 115, 101, 32, 116, 97, 103, 32, 102, 111, 117, 110, 100, 32, 102, 111, 114, 32, 114, 101, 118, 105, 115, 105, 111, 110, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [47, 114, 101, 108, 101, 97, 115, 101, 115, 47, 100, 111, 119, 110, 108, 111, 97, 100, 47, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 39, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5_value: LeanStringObject<76> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [114, 101, 108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 115, 105, 116, 111, 114, 121, 32, 85, 82, 76, 32, 110, 111, 116, 32, 107, 110, 111, 119, 110, 59, 32, 116, 104, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 109, 97, 121, 32, 110, 101, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 39, 114, 101, 108, 101, 97, 115, 101, 82, 101, 112, 111, 39, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5_value) as *mut LeanObject,3 as *mut LeanObject] };
static mut l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6_value
) as *mut LeanObject;
pub static l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 111, 117, 116, 45, 111, 102, 45, 100, 97, 116, 101, 32, 97, 110, 100, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 114, 101, 98, 117, 105, 108, 116, 0]};
static mut l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__0_value) as *mut LeanObject,3 as *mut LeanObject] };
static mut l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 111, 98, 117, 105, 108, 100, 0]};
static mut l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1_value:
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
static mut l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [60, 104, 97, 115, 104, 62, 0],
};
static mut l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2_value
) as *mut LeanObject;
static mut l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instToStringBool___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instToJsonBool___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1_value) as *mut LeanObject] };
static mut l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_Lake_formatQuery___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2_value) as *mut LeanObject] };
static mut l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 101, 116, 99, 104, 32, 0]};
static mut l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lake_instQueryTextUnit___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lake_instQueryJsonUnit___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1_value) as *mut LeanObject] };
static mut l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_Lake_formatQuery___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2_value) as *mut LeanObject] };
static mut l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 101, 116, 99, 104, 32, 98, 117,
            105, 108, 100, 32, 99, 97, 99, 104, 101, 0,
        ],
    };
static mut l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_Package_buildCacheFacetConfig___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_buildCacheFacetConfig___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_buildCacheFacetConfig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_buildCacheFacetConfig___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Package_buildCacheFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [98, 117, 105, 108, 100, 46, 98, 97, 114, 114, 101, 108, 0],
    };
static mut l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_Package_optBarrelFacetConfig___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_optBarrelFacetConfig___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_optBarrelFacetConfig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_optBarrelFacetConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Package_optBarrelFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Package_barrelFacetConfig___lam__1___closed__0_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 101, 116, 99, 104, 32, 82, 101,
            115, 101, 114, 118, 111, 105, 114, 32, 98, 117, 105, 108, 100, 0,
        ],
    };
static mut l_Lake_Package_barrelFacetConfig___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_barrelFacetConfig___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_Package_barrelFacetConfig___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_barrelFacetConfig___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_barrelFacetConfig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_barrelFacetConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Package_barrelFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Package_optGitHubReleaseFacetConfig___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_Package_optGitHubReleaseFacetConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_optGitHubReleaseFacetConfig___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_optGitHubReleaseFacetConfig___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Package_optGitHubReleaseFacetConfig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0_value: LeanStringObject<
    31,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 101, 116, 99, 104, 32, 71, 105, 116,
        72, 117, 98, 32, 114, 101, 108, 101, 97, 115, 101, 0,
    ],
};
static mut l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_gitHubReleaseFacetConfig___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_gitHubReleaseFacetConfig___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Package_gitHubReleaseFacetConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_initFacetConfigs___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Package_initFacetConfigs___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Package_initFacetConfigs: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_initPackageFacetConfigs: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    v___x_3423_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__2;
    v___x_3424_ = l_Lake_BuildTrace_nil(v___x_3423_);
    return v___x_3424_;
}
pub unsafe fn _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    v___x_3425_ = lean_unsigned_to_nat(0);
    v___x_3426_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once
        ),
        _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3,
    );
    v___x_3427_ = 0;
    v___x_3428_ = 0;
    v___x_3429_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0;
    v___x_3430_ = lean_alloc_ctor(0, 3, (2) as u32);
    lean_ctor_set(v___x_3430_, 0, v___x_3429_);
    lean_ctor_set(v___x_3430_, 1, v___x_3426_);
    lean_ctor_set(v___x_3430_, 2, v___x_3425_);
    lean_ctor_set_uint8(
        v___x_3430_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3428_,
    );
    lean_ctor_set_uint8(
        v___x_3430_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
        v___x_3427_,
    );
    return v___x_3430_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(
    mut v_self_3431_: *mut LeanObject,
    mut v_a_3432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depPkgs_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    v_depPkgs_3434_ = lean_ctor_get(v_self_3431_, 13);
    v___x_3435_ = lean_box(0);
    v___x_3436_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
    v___x_3437_ = 0;
    v___x_3438_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4_once
        ),
        _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4,
    );
    lean_inc_ref(v_depPkgs_3434_);
    v___x_3439_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3439_, 0, v_depPkgs_3434_);
    lean_ctor_set(v___x_3439_, 1, v___x_3438_);
    v___x_3440_ = lean_task_pure(v___x_3439_);
    v___x_3441_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_3441_, 0, v___x_3440_);
    lean_ctor_set(v___x_3441_, 1, v___x_3435_);
    lean_ctor_set(v___x_3441_, 2, v___x_3436_);
    lean_ctor_set_uint8(
        v___x_3441_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3437_,
    );
    v___x_3442_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3442_, 0, v___x_3441_);
    lean_ctor_set(v___x_3442_, 1, v_a_3432_);
    return v___x_3442_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___boxed(
    mut v_self_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3446_: *mut LeanObject = core::ptr::null_mut();
    v_res_3446_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(
        v_self_3443_,
        v_a_3444_,
    );
    lean_dec_ref(v_self_3443_);
    return v_res_3446_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(
    mut v_self_3447_: *mut LeanObject,
    mut v_a_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
    mut v_a_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
    mut v_a_3452_: *mut LeanObject,
    mut v_a_3453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    v___x_3455_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(
        v_self_3447_,
        v_a_3453_,
    );
    return v___x_3455_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___boxed(
    mut v_self_3456_: *mut LeanObject,
    mut v_a_3457_: *mut LeanObject,
    mut v_a_3458_: *mut LeanObject,
    mut v_a_3459_: *mut LeanObject,
    mut v_a_3460_: *mut LeanObject,
    mut v_a_3461_: *mut LeanObject,
    mut v_a_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3464_: *mut LeanObject = core::ptr::null_mut();
    v_res_3464_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(
        v_self_3456_,
        v_a_3457_,
        v_a_3458_,
        v_a_3459_,
        v_a_3460_,
        v_a_3461_,
        v_a_3462_,
    );
    lean_dec_ref(v_a_3461_);
    lean_dec(v_a_3460_);
    lean_dec(v_a_3459_);
    lean_dec(v_a_3458_);
    lean_dec_ref(v_a_3457_);
    lean_dec_ref(v_self_3456_);
    return v_res_3464_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(
    mut v_sz_3465_: usize,
    mut v_i_3466_: usize,
    mut v_bs_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3468_: u8 = 0;
    let mut v_v_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: usize = 0;
    let mut v___x_3476_: usize = 0;
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3468_ = lean_usize_dec_lt(v_i_3466_, v_sz_3465_);
                if v___x_3468_ == 0 {
                    return v_bs_3467_;
                } else {
                    v_v_3469_ = lean_array_uget_borrowed(v_bs_3467_, v_i_3466_);
                    v_keyName_3470_ = lean_ctor_get(v_v_3469_, 2);
                    lean_inc(v_keyName_3470_);
                    v___x_3471_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3472_ = lean_array_uset(v_bs_3467_, v_i_3466_, v___x_3471_);
                    v___x_3473_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_keyName_3470_,
                        v___x_3468_,
                    );
                    v___x_3474_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3474_, 0, v___x_3473_);
                    v___x_3475_ = 1usize;
                    v___x_3476_ = lean_usize_add(v_i_3466_, v___x_3475_);
                    v___x_3477_ = lean_array_uset(v_bs_x27_3472_, v_i_3466_, v___x_3474_);
                    v_i_3466_ = v___x_3476_;
                    v_bs_3467_ = v___x_3477_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1___boxed(
    mut v_sz_3479_: *mut LeanObject,
    mut v_i_3480_: *mut LeanObject,
    mut v_bs_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3482_: usize = 0;
    let mut v_i_boxed_3483_: usize = 0;
    let mut v_res_3484_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3482_ = lean_unbox_usize(v_sz_3479_);
    lean_dec(v_sz_3479_);
    v_i_boxed_3483_ = lean_unbox_usize(v_i_3480_);
    lean_dec(v_i_3480_);
    v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_boxed_3482_, v_i_boxed_3483_, v_bs_3481_);
    return v_res_3484_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(
    mut v_as_3486_: *mut LeanObject,
    mut v_i_3487_: usize,
    mut v_stop_3488_: usize,
    mut v_b_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: usize = 0;
    let mut v___x_3498_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3490_ = lean_usize_dec_eq(v_i_3487_, v_stop_3488_);
                if v___x_3490_ == 0 {
                    v___x_3491_ = lean_array_uget_borrowed(v_as_3486_, v_i_3487_);
                    v_baseName_3492_ = lean_ctor_get(v___x_3491_, 1);
                    lean_inc(v_baseName_3492_);
                    v___x_3493_ = l_Lean_Name_toString(v_baseName_3492_, v___x_3490_);
                    v___x_3494_ = lean_string_append(v_b_3489_, v___x_3493_);
                    lean_dec_ref(v___x_3493_);
                    v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0;
                    v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
                    v___x_3497_ = 1usize;
                    v___x_3498_ = lean_usize_add(v_i_3487_, v___x_3497_);
                    v_i_3487_ = v___x_3498_;
                    v_b_3489_ = v___x_3496_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3489_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(
    mut v_as_3500_: *mut LeanObject,
    mut v_i_3501_: *mut LeanObject,
    mut v_stop_3502_: *mut LeanObject,
    mut v_b_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3504_: usize = 0;
    let mut v_stop_boxed_3505_: usize = 0;
    let mut v_res_3506_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3504_ = lean_unbox_usize(v_i_3501_);
    lean_dec(v_i_3501_);
    v_stop_boxed_3505_ = lean_unbox_usize(v_stop_3502_);
    lean_dec(v_stop_3502_);
    v_res_3506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_as_3500_, v_i_boxed_3504_, v_stop_boxed_3505_, v_b_3503_);
    lean_dec_ref(v_as_3500_);
    return v_res_3506_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(
    mut v_fmt_3507_: u8,
    mut v_a_3508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: u8 = 0;
    let mut v___x_3522_: usize = 0;
    let mut v___x_3523_: usize = 0;
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: usize = 0;
    let mut v___x_3526_: usize = 0;
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3528_: usize = 0;
    let mut v___x_3529_: usize = 0;
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_fmt_3507_ == 0 {
                    v___x_3517_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                    v___x_3518_ = lean_unsigned_to_nat(0);
                    v___x_3519_ = lean_array_get_size(v_a_3508_);
                    v___x_3520_ = lean_nat_dec_lt(v___x_3518_, v___x_3519_);
                    if v___x_3520_ == 0 {
                        lean_dec_ref(v_a_3508_);
                        v___y_3510_ = v___x_3517_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3521_ = lean_nat_dec_le(v___x_3519_, v___x_3519_);
                        if v___x_3521_ == 0 {
                            if v___x_3520_ == 0 {
                                lean_dec_ref(v_a_3508_);
                                v___y_3510_ = v___x_3517_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3522_ = 0usize;
                                v___x_3523_ = lean_usize_of_nat(v___x_3519_);
                                v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_a_3508_, v___x_3522_, v___x_3523_, v___x_3517_);
                                lean_dec_ref(v_a_3508_);
                                v___y_3510_ = v___x_3524_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_3525_ = 0usize;
                            v___x_3526_ = lean_usize_of_nat(v___x_3519_);
                            v___x_3527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_a_3508_, v___x_3525_, v___x_3526_, v___x_3517_);
                            lean_dec_ref(v_a_3508_);
                            v___y_3510_ = v___x_3527_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_sz_3528_ = lean_array_size(v_a_3508_);
                    v___x_3529_ = 0usize;
                    v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_3528_, v___x_3529_, v_a_3508_);
                    v___x_3531_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v___x_3531_, 0, v___x_3530_);
                    v___x_3532_ = l_Lean_Json_compress(v___x_3531_);
                    return v___x_3532_;
                }
            }
            1 => {
                v___x_3511_ = lean_unsigned_to_nat(1);
                v___x_3512_ = lean_unsigned_to_nat(0);
                v___x_3513_ = lean_string_utf8_byte_size(v___y_3510_);
                lean_inc_ref(v___y_3510_);
                v___x_3514_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3514_, 0, v___y_3510_);
                lean_ctor_set(v___x_3514_, 1, v___x_3512_);
                lean_ctor_set(v___x_3514_, 2, v___x_3513_);
                v___x_3515_ = l_String_Slice_Pos_prevn(v___x_3514_, v___x_3513_, v___x_3511_);
                lean_dec_ref_known(v___x_3514_, 3);
                v___x_3516_ = lean_string_utf8_extract(v___y_3510_, v___x_3512_, v___x_3515_);
                lean_dec(v___x_3515_);
                lean_dec_ref(v___y_3510_);
                return v___x_3516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0___boxed(
    mut v_fmt_3533_: *mut LeanObject,
    mut v_a_3534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_3535_: u8 = 0;
    let mut v_res_3536_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_3535_ = (lean_unbox(v_fmt_3533_) as u8);
    v_res_3536_ = l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(
        v_fmt_boxed_3535_,
        v_a_3534_,
    );
    return v_res_3536_;
}
pub unsafe fn _init_l_Lake_Package_depsFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___x_3539_: u8 = 0;
    let mut v___f_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    v___x_3539_ = 1;
    v___f_3540_ = l_Lake_Package_depsFacetConfig___closed__0;
    v___x_3541_ = 0;
    v___x_3542_ = lean_box(0);
    v___x_3543_ = l_Lake_Package_depsFacetConfig___closed__1;
    v___x_3544_ = l_Lake_Package_keyword;
    v___x_3545_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_3545_, 0, v___x_3544_);
    lean_ctor_set(v___x_3545_, 1, v___x_3543_);
    lean_ctor_set(v___x_3545_, 2, v___x_3542_);
    lean_ctor_set(v___x_3545_, 3, v___f_3540_);
    lean_ctor_set_uint8(
        v___x_3545_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_3541_,
    );
    lean_ctor_set_uint8(
        v___x_3545_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_3539_,
    );
    return v___x_3545_;
}
pub unsafe fn _init_l_Lake_Package_depsFacetConfig() -> *mut LeanObject {
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    v___x_3546_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_depsFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Package_depsFacetConfig___closed__2_once),
        _init_l_Lake_Package_depsFacetConfig___closed__2,
    );
    return v___x_3546_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    v___x_3547_ = lean_box(0);
    v___x_3548_ = lean_unsigned_to_nat(16);
    v___x_3549_ = lean_mk_array(v___x_3548_, v___x_3547_);
    return v___x_3549_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    v___x_3550_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0);
    v___x_3551_ = lean_unsigned_to_nat(0);
    v___x_3552_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3552_, 0, v___x_3551_);
    lean_ctor_set(v___x_3552_, 1, v___x_3550_);
    return v___x_3552_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2;
    v___x_3556_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1);
    v___x_3557_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3557_, 0, v___x_3556_);
    lean_ctor_set(v___x_3557_, 1, v___x_3555_);
    return v___x_3557_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2()
-> *mut LeanObject {
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    v___x_3558_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3);
    return v___x_3558_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(
    mut v_a_3559_: *mut LeanObject,
    mut v_x_3560_: *mut LeanObject,
) -> u8 {
    let mut v___x_3561_: u8 = 0;
    let mut v_key_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wsIdx_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wsIdx_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3560_) == 0 {
                    v___x_3561_ = 0;
                    return v___x_3561_;
                } else {
                    v_key_3562_ = lean_ctor_get(v_x_3560_, 0);
                    v_tail_3563_ = lean_ctor_get(v_x_3560_, 2);
                    v_wsIdx_3564_ = lean_ctor_get(v_key_3562_, 0);
                    v_wsIdx_3565_ = lean_ctor_get(v_a_3559_, 0);
                    v___x_3566_ = lean_nat_dec_eq(v_wsIdx_3564_, v_wsIdx_3565_);
                    if v___x_3566_ == 0 {
                        v_x_3560_ = v_tail_3563_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3566_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_a_3568_: *mut LeanObject,
    mut v_x_3569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3570_: u8 = 0;
    let mut v_r_3571_: *mut LeanObject = core::ptr::null_mut();
    v_res_3570_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_3568_, v_x_3569_);
    lean_dec(v_x_3569_);
    lean_dec_ref(v_a_3568_);
    v_r_3571_ = lean_box((v_res_3570_) as usize);
    return v_r_3571_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: u64 = 0;
    v___x_3572_ = lean_unsigned_to_nat(1723);
    v___x_3573_ = lean_uint64_of_nat(v___x_3572_);
    return v___x_3573_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(
    mut v_m_3574_: *mut LeanObject,
    mut v_a_3575_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: u64 = 0;
    let mut v___x_3581_: u64 = 0;
    let mut v___x_3582_: u64 = 0;
    let mut v_fold_3583_: u64 = 0;
    let mut v___x_3584_: u64 = 0;
    let mut v___x_3585_: u64 = 0;
    let mut v___x_3586_: u64 = 0;
    let mut v___x_3587_: usize = 0;
    let mut v___x_3588_: usize = 0;
    let mut v___x_3589_: usize = 0;
    let mut v___x_3590_: usize = 0;
    let mut v___x_3591_: usize = 0;
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    let mut v___x_3594_: u64 = 0;
    let mut v_hash_3595_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3576_ = lean_ctor_get(v_m_3574_, 1);
                v_keyName_3577_ = lean_ctor_get(v_a_3575_, 2);
                v___x_3578_ = lean_array_get_size(v_buckets_3576_);
                if lean_obj_tag(v_keyName_3577_) == 0 {
                    v___x_3594_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
                    v___y_3580_ = v___x_3594_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3595_ = lean_ctor_get_uint64(
                        v_keyName_3577_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3580_ = v_hash_3595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3581_ = 32u64;
                v___x_3582_ = lean_uint64_shift_right(v___y_3580_, v___x_3581_);
                v_fold_3583_ = lean_uint64_xor(v___y_3580_, v___x_3582_);
                v___x_3584_ = 16u64;
                v___x_3585_ = lean_uint64_shift_right(v_fold_3583_, v___x_3584_);
                v___x_3586_ = lean_uint64_xor(v_fold_3583_, v___x_3585_);
                v___x_3587_ = lean_uint64_to_usize(v___x_3586_);
                v___x_3588_ = lean_usize_of_nat(v___x_3578_);
                v___x_3589_ = 1usize;
                v___x_3590_ = lean_usize_sub(v___x_3588_, v___x_3589_);
                v___x_3591_ = lean_usize_land(v___x_3587_, v___x_3590_);
                v___x_3592_ = lean_array_uget_borrowed(v_buckets_3576_, v___x_3591_);
                v___x_3593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_3575_, v___x_3592_);
                return v___x_3593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(
    mut v_m_3596_: *mut LeanObject,
    mut v_a_3597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3598_: u8 = 0;
    let mut v_r_3599_: *mut LeanObject = core::ptr::null_mut();
    v_res_3598_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_3596_, v_a_3597_);
    lean_dec_ref(v_a_3597_);
    lean_dec_ref(v_m_3596_);
    v_r_3599_ = lean_box((v_res_3598_) as usize);
    return v_r_3599_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(
    mut v_x_3600_: *mut LeanObject,
    mut v_x_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3607_: u8 = 0;
    let mut v_keyName_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3611_: u64 = 0;
    let mut v___x_3612_: u64 = 0;
    let mut v___x_3613_: u64 = 0;
    let mut v_fold_3614_: u64 = 0;
    let mut v___x_3615_: u64 = 0;
    let mut v___x_3616_: u64 = 0;
    let mut v___x_3617_: u64 = 0;
    let mut v___x_3618_: usize = 0;
    let mut v___x_3619_: usize = 0;
    let mut v___x_3620_: usize = 0;
    let mut v___x_3621_: usize = 0;
    let mut v___x_3622_: usize = 0;
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u64 = 0;
    let mut v_hash_3630_: u64 = 0;
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3601_) == 0 {
                    return v_x_3600_;
                } else {
                    v_key_3602_ = lean_ctor_get(v_x_3601_, 0);
                    v_value_3603_ = lean_ctor_get(v_x_3601_, 1);
                    v_tail_3604_ = lean_ctor_get(v_x_3601_, 2);
                    v_isSharedCheck_3631_ = (!lean_is_exclusive(v_x_3601_)) as u8;
                    if v_isSharedCheck_3631_ == 0 {
                        v___x_3606_ = v_x_3601_;
                        v_isShared_3607_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3604_);
                        lean_inc(v_value_3603_);
                        lean_inc(v_key_3602_);
                        lean_dec(v_x_3601_);
                        v___x_3606_ = lean_box(0);
                        v_isShared_3607_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_keyName_3608_ = lean_ctor_get(v_key_3602_, 2);
                v___x_3609_ = lean_array_get_size(v_x_3600_);
                if lean_obj_tag(v_keyName_3608_) == 0 {
                    v___x_3629_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
                    v___y_3611_ = v___x_3629_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3630_ = lean_ctor_get_uint64(
                        v_keyName_3608_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3611_ = v_hash_3630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3612_ = 32u64;
                v___x_3613_ = lean_uint64_shift_right(v___y_3611_, v___x_3612_);
                v_fold_3614_ = lean_uint64_xor(v___y_3611_, v___x_3613_);
                v___x_3615_ = 16u64;
                v___x_3616_ = lean_uint64_shift_right(v_fold_3614_, v___x_3615_);
                v___x_3617_ = lean_uint64_xor(v_fold_3614_, v___x_3616_);
                v___x_3618_ = lean_uint64_to_usize(v___x_3617_);
                v___x_3619_ = lean_usize_of_nat(v___x_3609_);
                v___x_3620_ = 1usize;
                v___x_3621_ = lean_usize_sub(v___x_3619_, v___x_3620_);
                v___x_3622_ = lean_usize_land(v___x_3618_, v___x_3621_);
                v___x_3623_ = lean_array_uget_borrowed(v_x_3600_, v___x_3622_);
                lean_inc(v___x_3623_);
                if v_isShared_3607_ == 0 {
                    lean_ctor_set(v___x_3606_, 2, v___x_3623_);
                    v___x_3625_ = v___x_3606_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_key_3602_);
                    lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_value_3603_);
                    lean_ctor_set(v_reuseFailAlloc_3628_, 2, v___x_3623_);
                    v___x_3625_ = v_reuseFailAlloc_3628_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3626_ = lean_array_uset(v_x_3600_, v___x_3622_, v___x_3625_);
                v_x_3600_ = v___x_3626_;
                v_x_3601_ = v_tail_3604_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(
    mut v_i_3632_: *mut LeanObject,
    mut v_source_3633_: *mut LeanObject,
    mut v_target_3634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v_es_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3635_ = lean_array_get_size(v_source_3633_);
                v___x_3636_ = lean_nat_dec_lt(v_i_3632_, v___x_3635_);
                if v___x_3636_ == 0 {
                    lean_dec_ref(v_source_3633_);
                    lean_dec(v_i_3632_);
                    return v_target_3634_;
                } else {
                    v_es_3637_ = lean_array_fget(v_source_3633_, v_i_3632_);
                    v___x_3638_ = lean_box(0);
                    v_source_3639_ = lean_array_fset(v_source_3633_, v_i_3632_, v___x_3638_);
                    v_target_3640_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_target_3634_, v_es_3637_);
                    v___x_3641_ = lean_unsigned_to_nat(1);
                    v___x_3642_ = lean_nat_add(v_i_3632_, v___x_3641_);
                    lean_dec(v_i_3632_);
                    v_i_3632_ = v___x_3642_;
                    v_source_3633_ = v_source_3639_;
                    v_target_3634_ = v_target_3640_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(
    mut v_data_3644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    v___x_3645_ = lean_array_get_size(v_data_3644_);
    v___x_3646_ = lean_unsigned_to_nat(2);
    v_nbuckets_3647_ = lean_nat_mul(v___x_3645_, v___x_3646_);
    v___x_3648_ = lean_unsigned_to_nat(0);
    v___x_3649_ = lean_box(0);
    v___x_3650_ = lean_mk_array(v_nbuckets_3647_, v___x_3649_);
    v___x_3651_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v___x_3648_, v_data_3644_, v___x_3650_);
    return v___x_3651_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(
    mut v_m_3652_: *mut LeanObject,
    mut v_a_3653_: *mut LeanObject,
    mut v_b_3654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3660_: u64 = 0;
    let mut v___x_3661_: u64 = 0;
    let mut v___x_3662_: u64 = 0;
    let mut v_fold_3663_: u64 = 0;
    let mut v___x_3664_: u64 = 0;
    let mut v___x_3665_: u64 = 0;
    let mut v___x_3666_: u64 = 0;
    let mut v___x_3667_: usize = 0;
    let mut v___x_3668_: usize = 0;
    let mut v___x_3669_: usize = 0;
    let mut v___x_3670_: usize = 0;
    let mut v___x_3671_: usize = 0;
    let mut v_bkt_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: u8 = 0;
    let mut v_val_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_unused_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: u64 = 0;
    let mut v_hash_3698_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3655_ = lean_ctor_get(v_m_3652_, 0);
                v_buckets_3656_ = lean_ctor_get(v_m_3652_, 1);
                v_keyName_3657_ = lean_ctor_get(v_a_3653_, 2);
                v___x_3658_ = lean_array_get_size(v_buckets_3656_);
                if lean_obj_tag(v_keyName_3657_) == 0 {
                    v___x_3697_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
                    v___y_3660_ = v___x_3697_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3698_ = lean_ctor_get_uint64(
                        v_keyName_3657_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3660_ = v_hash_3698_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3661_ = 32u64;
                v___x_3662_ = lean_uint64_shift_right(v___y_3660_, v___x_3661_);
                v_fold_3663_ = lean_uint64_xor(v___y_3660_, v___x_3662_);
                v___x_3664_ = 16u64;
                v___x_3665_ = lean_uint64_shift_right(v_fold_3663_, v___x_3664_);
                v___x_3666_ = lean_uint64_xor(v_fold_3663_, v___x_3665_);
                v___x_3667_ = lean_uint64_to_usize(v___x_3666_);
                v___x_3668_ = lean_usize_of_nat(v___x_3658_);
                v___x_3669_ = 1usize;
                v___x_3670_ = lean_usize_sub(v___x_3668_, v___x_3669_);
                v___x_3671_ = lean_usize_land(v___x_3667_, v___x_3670_);
                v_bkt_3672_ = lean_array_uget_borrowed(v_buckets_3656_, v___x_3671_);
                v___x_3673_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_3653_, v_bkt_3672_);
                if v___x_3673_ == 0 {
                    lean_inc_ref(v_buckets_3656_);
                    lean_inc(v_size_3655_);
                    v_isSharedCheck_3694_ = (!lean_is_exclusive(v_m_3652_)) as u8;
                    if v_isSharedCheck_3694_ == 0 {
                        v_unused_3695_ = lean_ctor_get(v_m_3652_, 1);
                        lean_dec(v_unused_3695_);
                        v_unused_3696_ = lean_ctor_get(v_m_3652_, 0);
                        lean_dec(v_unused_3696_);
                        v___x_3675_ = v_m_3652_;
                        v_isShared_3676_ = v_isSharedCheck_3694_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_3652_);
                        v___x_3675_ = lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_3694_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_3654_);
                    lean_dec_ref(v_a_3653_);
                    return v_m_3652_;
                }
            }
            2 => {
                v___x_3677_ = lean_unsigned_to_nat(1);
                v_size_x27_3678_ = lean_nat_add(v_size_3655_, v___x_3677_);
                lean_dec(v_size_3655_);
                lean_inc(v_bkt_3672_);
                v___x_3679_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3679_, 0, v_a_3653_);
                lean_ctor_set(v___x_3679_, 1, v_b_3654_);
                lean_ctor_set(v___x_3679_, 2, v_bkt_3672_);
                v_buckets_x27_3680_ = lean_array_uset(v_buckets_3656_, v___x_3671_, v___x_3679_);
                v___x_3681_ = lean_unsigned_to_nat(4);
                v___x_3682_ = lean_nat_mul(v_size_x27_3678_, v___x_3681_);
                v___x_3683_ = lean_unsigned_to_nat(3);
                v___x_3684_ = lean_nat_div(v___x_3682_, v___x_3683_);
                lean_dec(v___x_3682_);
                v___x_3685_ = lean_array_get_size(v_buckets_x27_3680_);
                v___x_3686_ = lean_nat_dec_le(v___x_3684_, v___x_3685_);
                lean_dec(v___x_3684_);
                if v___x_3686_ == 0 {
                    v_val_3687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_buckets_x27_3680_);
                    if v_isShared_3676_ == 0 {
                        lean_ctor_set(v___x_3675_, 1, v_val_3687_);
                        lean_ctor_set(v___x_3675_, 0, v_size_x27_3678_);
                        v___x_3689_ = v___x_3675_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_size_x27_3678_);
                        lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_val_3687_);
                        v___x_3689_ = v_reuseFailAlloc_3690_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3676_ == 0 {
                        lean_ctor_set(v___x_3675_, 1, v_buckets_x27_3680_);
                        lean_ctor_set(v___x_3675_, 0, v_size_x27_3678_);
                        v___x_3692_ = v___x_3675_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_size_x27_3678_);
                        lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_buckets_x27_3680_);
                        v___x_3692_ = v_reuseFailAlloc_3693_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3689_;
            }
            4 => {
                return v___x_3692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(
    mut v_self_3699_: *mut LeanObject,
    mut v_a_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toHashSet_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toArray_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: u8 = 0;
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3713_: u8 = 0;
    let mut v_unused_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toHashSet_3701_ = lean_ctor_get(v_self_3699_, 0);
                v_toArray_3702_ = lean_ctor_get(v_self_3699_, 1);
                v___x_3703_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_toHashSet_3701_, v_a_3700_);
                if v___x_3703_ == 0 {
                    lean_inc_ref(v_toArray_3702_);
                    lean_inc_ref(v_toHashSet_3701_);
                    v_isSharedCheck_3713_ = (!lean_is_exclusive(v_self_3699_)) as u8;
                    if v_isSharedCheck_3713_ == 0 {
                        v_unused_3714_ = lean_ctor_get(v_self_3699_, 1);
                        lean_dec(v_unused_3714_);
                        v_unused_3715_ = lean_ctor_get(v_self_3699_, 0);
                        lean_dec(v_unused_3715_);
                        v___x_3705_ = v_self_3699_;
                        v_isShared_3706_ = v_isSharedCheck_3713_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_self_3699_);
                        v___x_3705_ = lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3713_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_3700_);
                    return v_self_3699_;
                }
            }
            1 => {
                v___x_3707_ = lean_box(0);
                lean_inc_ref(v_a_3700_);
                v___x_3708_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_toHashSet_3701_, v_a_3700_, v___x_3707_);
                v___x_3709_ = lean_array_push(v_toArray_3702_, v_a_3700_);
                if v_isShared_3706_ == 0 {
                    lean_ctor_set(v___x_3705_, 1, v___x_3709_);
                    lean_ctor_set(v___x_3705_, 0, v___x_3708_);
                    v___x_3711_ = v___x_3705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3708_);
                    lean_ctor_set(v_reuseFailAlloc_3712_, 1, v___x_3709_);
                    v___x_3711_ = v_reuseFailAlloc_3712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(
    mut v_as_3716_: *mut LeanObject,
    mut v_i_3717_: usize,
    mut v_stop_3718_: usize,
    mut v_b_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3720_: u8 = 0;
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: usize = 0;
    let mut v___x_3724_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3720_ = lean_usize_dec_eq(v_i_3717_, v_stop_3718_);
                if v___x_3720_ == 0 {
                    v___x_3721_ = lean_array_uget_borrowed(v_as_3716_, v_i_3717_);
                    lean_inc(v___x_3721_);
                    v___x_3722_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v_b_3719_, v___x_3721_);
                    v___x_3723_ = 1usize;
                    v___x_3724_ = lean_usize_add(v_i_3717_, v___x_3723_);
                    v_i_3717_ = v___x_3724_;
                    v_b_3719_ = v___x_3722_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3719_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(
    mut v_as_3726_: *mut LeanObject,
    mut v_i_3727_: *mut LeanObject,
    mut v_stop_3728_: *mut LeanObject,
    mut v_b_3729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3730_: usize = 0;
    let mut v_stop_boxed_3731_: usize = 0;
    let mut v_res_3732_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3730_ = lean_unbox_usize(v_i_3727_);
    lean_dec(v_i_3727_);
    v_stop_boxed_3731_ = lean_unbox_usize(v_stop_3728_);
    lean_dec(v_stop_3728_);
    v_res_3732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_3726_, v_i_boxed_3730_, v_stop_boxed_3731_, v_b_3729_);
    lean_dec_ref(v_as_3726_);
    return v_res_3732_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(
    mut v_as_3733_: *mut LeanObject,
    mut v_i_3734_: usize,
    mut v_stop_3735_: usize,
    mut v_b_3736_: *mut LeanObject,
    mut v___y_3737_: *mut LeanObject,
    mut v___y_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: usize = 0;
    let mut v___x_3761_: usize = 0;
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: u8 = 0;
    let mut v___x_3766_: u8 = 0;
    let mut v___x_3767_: usize = 0;
    let mut v___x_3768_: usize = 0;
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: usize = 0;
    let mut v___x_3771_: usize = 0;
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v_a_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3786_: u8 = 0;
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3744_ = lean_usize_dec_eq(v_i_3734_, v_stop_3735_);
                if v___x_3744_ == 0 {
                    v___x_3745_ = lean_array_uget_borrowed(v_as_3733_, v_i_3734_);
                    v_keyName_3746_ = lean_ctor_get(v___x_3745_, 2);
                    v___x_3747_ = l_Lake_Package_transDepsFacet;
                    lean_inc(v_keyName_3746_);
                    v___x_3748_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3748_, 0, v_keyName_3746_);
                    v___x_3749_ = l_Lake_Package_keyword;
                    lean_inc(v___x_3745_);
                    v___x_3750_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v___x_3750_, 0, v___x_3748_);
                    lean_ctor_set(v___x_3750_, 1, v___x_3749_);
                    lean_ctor_set(v___x_3750_, 2, v___x_3745_);
                    lean_ctor_set(v___x_3750_, 3, v___x_3747_);
                    lean_inc_ref(v___y_3737_);
                    lean_inc_ref(v___y_3741_);
                    lean_inc(v___y_3740_);
                    lean_inc(v___y_3739_);
                    lean_inc(v___y_3738_);
                    v___x_3751_ = lean_apply_7(
                        v___y_3737_,
                        v___x_3750_,
                        v___y_3738_,
                        v___y_3739_,
                        v___y_3740_,
                        v___y_3741_,
                        v___y_3742_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3751_) == 0 {
                        v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
                        lean_inc(v_a_3752_);
                        v_a_3753_ = lean_ctor_get(v___x_3751_, 1);
                        lean_inc(v_a_3753_);
                        lean_dec_ref_known(v___x_3751_, 2);
                        v___x_3754_ = l_Lake_Job_await___redArg(v_a_3752_, v_a_3753_);
                        if lean_obj_tag(v___x_3754_) == 0 {
                            v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
                            lean_inc(v_a_3755_);
                            v_a_3756_ = lean_ctor_get(v___x_3754_, 1);
                            lean_inc(v_a_3756_);
                            lean_dec_ref_known(v___x_3754_, 2);
                            v___x_3763_ = lean_unsigned_to_nat(0);
                            v___x_3764_ = lean_array_get_size(v_a_3755_);
                            v___x_3765_ = lean_nat_dec_lt(v___x_3763_, v___x_3764_);
                            if v___x_3765_ == 0 {
                                lean_dec(v_a_3755_);
                                v___y_3758_ = v_b_3736_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3766_ = lean_nat_dec_le(v___x_3764_, v___x_3764_);
                                if v___x_3766_ == 0 {
                                    if v___x_3765_ == 0 {
                                        lean_dec(v_a_3755_);
                                        v___y_3758_ = v_b_3736_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3767_ = 0usize;
                                        v___x_3768_ = lean_usize_of_nat(v___x_3764_);
                                        v___x_3769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_3755_, v___x_3767_, v___x_3768_, v_b_3736_);
                                        lean_dec(v_a_3755_);
                                        v___y_3758_ = v___x_3769_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___x_3770_ = 0usize;
                                    v___x_3771_ = lean_usize_of_nat(v___x_3764_);
                                    v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_3755_, v___x_3770_, v___x_3771_, v_b_3736_);
                                    lean_dec(v_a_3755_);
                                    v___y_3758_ = v___x_3772_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___y_3737_);
                            lean_dec_ref(v_b_3736_);
                            v_a_3773_ = lean_ctor_get(v___x_3754_, 0);
                            v_a_3774_ = lean_ctor_get(v___x_3754_, 1);
                            v_isSharedCheck_3781_ = (!lean_is_exclusive(v___x_3754_)) as u8;
                            if v_isSharedCheck_3781_ == 0 {
                                v___x_3776_ = v___x_3754_;
                                v_isShared_3777_ = v_isSharedCheck_3781_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3774_);
                                lean_inc(v_a_3773_);
                                lean_dec(v___x_3754_);
                                v___x_3776_ = lean_box(0);
                                v_isShared_3777_ = v_isSharedCheck_3781_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_3737_);
                        lean_dec_ref(v_b_3736_);
                        v_a_3782_ = lean_ctor_get(v___x_3751_, 0);
                        v_a_3783_ = lean_ctor_get(v___x_3751_, 1);
                        v_isSharedCheck_3790_ = (!lean_is_exclusive(v___x_3751_)) as u8;
                        if v_isSharedCheck_3790_ == 0 {
                            v___x_3785_ = v___x_3751_;
                            v_isShared_3786_ = v_isSharedCheck_3790_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3783_);
                            lean_inc(v_a_3782_);
                            lean_dec(v___x_3751_);
                            v___x_3785_ = lean_box(0);
                            v_isShared_3786_ = v_isSharedCheck_3790_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3737_);
                    v___x_3791_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3791_, 0, v_b_3736_);
                    lean_ctor_set(v___x_3791_, 1, v___y_3742_);
                    return v___x_3791_;
                }
            }
            1 => {
                lean_inc(v___x_3745_);
                v___x_3759_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v___y_3758_, v___x_3745_);
                v___x_3760_ = 1usize;
                v___x_3761_ = lean_usize_add(v_i_3734_, v___x_3760_);
                v_i_3734_ = v___x_3761_;
                v_b_3736_ = v___x_3759_;
                v___y_3742_ = v_a_3756_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3777_ == 0 {
                    v___x_3779_ = v___x_3776_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3773_);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_a_3774_);
                    v___x_3779_ = v_reuseFailAlloc_3780_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3779_;
            }
            4 => {
                if v_isShared_3786_ == 0 {
                    v___x_3788_ = v___x_3785_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3782_);
                    lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_a_3783_);
                    v___x_3788_ = v_reuseFailAlloc_3789_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(
    mut v_as_3792_: *mut LeanObject,
    mut v_i_3793_: *mut LeanObject,
    mut v_stop_3794_: *mut LeanObject,
    mut v_b_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
    mut v___y_3798_: *mut LeanObject,
    mut v___y_3799_: *mut LeanObject,
    mut v___y_3800_: *mut LeanObject,
    mut v___y_3801_: *mut LeanObject,
    mut v___y_3802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3803_: usize = 0;
    let mut v_stop_boxed_3804_: usize = 0;
    let mut v_res_3805_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3803_ = lean_unbox_usize(v_i_3793_);
    lean_dec(v_i_3793_);
    v_stop_boxed_3804_ = lean_unbox_usize(v_stop_3794_);
    lean_dec(v_stop_3794_);
    v_res_3805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_3792_, v_i_boxed_3803_, v_stop_boxed_3804_, v_b_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
    lean_dec_ref(v___y_3800_);
    lean_dec(v___y_3799_);
    lean_dec(v___y_3798_);
    lean_dec(v___y_3797_);
    lean_dec_ref(v_as_3792_);
    return v_res_3805_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(
    mut v___x_3806_: *mut LeanObject,
    mut v___x_3807_: *mut LeanObject,
    mut v___x_3808_: *mut LeanObject,
    mut v___x_3809_: *mut LeanObject,
    mut v_depPkgs_3810_: *mut LeanObject,
    mut v___y_3811_: *mut LeanObject,
    mut v___y_3812_: *mut LeanObject,
    mut v___y_3813_: *mut LeanObject,
    mut v___y_3814_: *mut LeanObject,
    mut v___y_3815_: *mut LeanObject,
    mut v___y_3816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toArray_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3824_: u8 = 0;
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3828_: u8 = 0;
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_unused_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v___x_3852_: u8 = 0;
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: usize = 0;
    let mut v___x_3855_: usize = 0;
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: usize = 0;
    let mut v___x_3858_: usize = 0;
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3852_ = lean_nat_dec_lt(v___x_3806_, v___x_3808_);
                if v___x_3852_ == 0 {
                    lean_dec_ref(v___y_3811_);
                    v_a_3819_ = v___x_3809_;
                    v_a_3820_ = v___y_3816_;
                    state = 1;
                    continue;
                } else {
                    v___x_3853_ = lean_nat_dec_le(v___x_3808_, v___x_3808_);
                    if v___x_3853_ == 0 {
                        if v___x_3852_ == 0 {
                            lean_dec_ref(v___y_3811_);
                            v_a_3819_ = v___x_3809_;
                            v_a_3820_ = v___y_3816_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3854_ = 0usize;
                            v___x_3855_ = lean_usize_of_nat(v___x_3808_);
                            v___x_3856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_3810_, v___x_3854_, v___x_3855_, v___x_3809_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
                            v___y_3840_ = v___x_3856_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_3857_ = 0usize;
                        v___x_3858_ = lean_usize_of_nat(v___x_3808_);
                        v___x_3859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_3810_, v___x_3857_, v___x_3858_, v___x_3809_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
                        v___y_3840_ = v___x_3859_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_toArray_3821_ = lean_ctor_get(v_a_3819_, 1);
                v_isSharedCheck_3837_ = (!lean_is_exclusive(v_a_3819_)) as u8;
                if v_isSharedCheck_3837_ == 0 {
                    v_unused_3838_ = lean_ctor_get(v_a_3819_, 0);
                    lean_dec(v_unused_3838_);
                    v___x_3823_ = v_a_3819_;
                    v_isShared_3824_ = v_isSharedCheck_3837_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toArray_3821_);
                    lean_dec(v_a_3819_);
                    v___x_3823_ = lean_box(0);
                    v_isShared_3824_ = v_isSharedCheck_3837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3825_ = lean_mk_empty_array_with_capacity(v___x_3806_);
                v___x_3826_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                v___x_3827_ = 0;
                v___x_3828_ = 0;
                v___x_3829_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                v___x_3830_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_3830_, 0, v___x_3825_);
                lean_ctor_set(v___x_3830_, 1, v___x_3829_);
                lean_ctor_set(v___x_3830_, 2, v___x_3806_);
                lean_ctor_set_uint8(
                    v___x_3830_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3827_,
                );
                lean_ctor_set_uint8(
                    v___x_3830_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_3828_,
                );
                if v_isShared_3824_ == 0 {
                    lean_ctor_set(v___x_3823_, 1, v___x_3830_);
                    lean_ctor_set(v___x_3823_, 0, v_toArray_3821_);
                    v___x_3832_ = v___x_3823_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_toArray_3821_);
                    lean_ctor_set(v_reuseFailAlloc_3836_, 1, v___x_3830_);
                    v___x_3832_ = v_reuseFailAlloc_3836_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3833_ = lean_task_pure(v___x_3832_);
                v___x_3834_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3834_, 0, v___x_3833_);
                lean_ctor_set(v___x_3834_, 1, v___x_3807_);
                lean_ctor_set(v___x_3834_, 2, v___x_3826_);
                lean_ctor_set_uint8(
                    v___x_3834_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3828_,
                );
                v___x_3835_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3835_, 0, v___x_3834_);
                lean_ctor_set(v___x_3835_, 1, v_a_3820_);
                return v___x_3835_;
            }
            4 => {
                if lean_obj_tag(v___y_3840_) == 0 {
                    v_a_3841_ = lean_ctor_get(v___y_3840_, 0);
                    lean_inc(v_a_3841_);
                    v_a_3842_ = lean_ctor_get(v___y_3840_, 1);
                    lean_inc(v_a_3842_);
                    lean_dec_ref_known(v___y_3840_, 2);
                    v_a_3819_ = v_a_3841_;
                    v_a_3820_ = v_a_3842_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_3807_);
                    lean_dec(v___x_3806_);
                    v_a_3843_ = lean_ctor_get(v___y_3840_, 0);
                    v_a_3844_ = lean_ctor_get(v___y_3840_, 1);
                    v_isSharedCheck_3851_ = (!lean_is_exclusive(v___y_3840_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v___x_3846_ = v___y_3840_;
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3844_);
                        lean_inc(v_a_3843_);
                        lean_dec(v___y_3840_);
                        v___x_3846_ = lean_box(0);
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3847_ == 0 {
                    v___x_3849_ = v___x_3846_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3843_);
                    lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_a_3844_);
                    v___x_3849_ = v_reuseFailAlloc_3850_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(
    mut v___x_3860_: *mut LeanObject,
    mut v___x_3861_: *mut LeanObject,
    mut v___x_3862_: *mut LeanObject,
    mut v___x_3863_: *mut LeanObject,
    mut v_depPkgs_3864_: *mut LeanObject,
    mut v___y_3865_: *mut LeanObject,
    mut v___y_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3872_: *mut LeanObject = core::ptr::null_mut();
    v_res_3872_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(
        v___x_3860_,
        v___x_3861_,
        v___x_3862_,
        v___x_3863_,
        v_depPkgs_3864_,
        v___y_3865_,
        v___y_3866_,
        v___y_3867_,
        v___y_3868_,
        v___y_3869_,
        v___y_3870_,
    );
    lean_dec_ref(v___y_3869_);
    lean_dec(v___y_3868_);
    lean_dec(v___y_3867_);
    lean_dec(v___y_3866_);
    lean_dec_ref(v_depPkgs_3864_);
    lean_dec(v___x_3862_);
    return v_res_3872_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(
    mut v_self_3873_: *mut LeanObject,
    mut v_a_3874_: *mut LeanObject,
    mut v_a_3875_: *mut LeanObject,
    mut v_a_3876_: *mut LeanObject,
    mut v_a_3877_: *mut LeanObject,
    mut v_a_3878_: *mut LeanObject,
    mut v_a_3879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depPkgs_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    v_depPkgs_3881_ = lean_ctor_get(v_self_3873_, 13);
    lean_inc_ref(v_depPkgs_3881_);
    lean_dec_ref(v_self_3873_);
    v___x_3882_ = lean_box(0);
    v___x_3883_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
    v___x_3884_ = lean_unsigned_to_nat(0);
    v___x_3885_ = lean_array_get_size(v_depPkgs_3881_);
    v___f_3886_ = lean_alloc_closure(
        l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        5,
    );
    lean_closure_set(v___f_3886_, 0, v___x_3884_);
    lean_closure_set(v___f_3886_, 1, v___x_3882_);
    lean_closure_set(v___f_3886_, 2, v___x_3885_);
    lean_closure_set(v___f_3886_, 3, v___x_3883_);
    lean_closure_set(v___f_3886_, 4, v_depPkgs_3881_);
    v___x_3887_ = l_Lake_ensureJob___redArg(
        v___x_3882_,
        v___f_3886_,
        v_a_3874_,
        v_a_3875_,
        v_a_3876_,
        v_a_3877_,
        v_a_3878_,
        v_a_3879_,
    );
    return v___x_3887_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(
    mut v_self_3888_: *mut LeanObject,
    mut v_a_3889_: *mut LeanObject,
    mut v_a_3890_: *mut LeanObject,
    mut v_a_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
    mut v_a_3894_: *mut LeanObject,
    mut v_a_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3896_: *mut LeanObject = core::ptr::null_mut();
    v_res_3896_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(
        v_self_3888_,
        v_a_3889_,
        v_a_3890_,
        v_a_3891_,
        v_a_3892_,
        v_a_3893_,
        v_a_3894_,
    );
    lean_dec_ref(v_a_3893_);
    lean_dec(v_a_3892_);
    lean_dec(v_a_3891_);
    lean_dec(v_a_3890_);
    return v_res_3896_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(
    mut v_00_u03b2_3897_: *mut LeanObject,
    mut v_m_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
) -> u8 {
    let mut v___x_3900_: u8 = 0;
    v___x_3900_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_3898_, v_a_3899_);
    return v___x_3900_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(
    mut v_00_u03b2_3901_: *mut LeanObject,
    mut v_m_3902_: *mut LeanObject,
    mut v_a_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3904_: u8 = 0;
    let mut v_r_3905_: *mut LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_3901_, v_m_3902_, v_a_3903_);
    lean_dec_ref(v_a_3903_);
    lean_dec_ref(v_m_3902_);
    v_r_3905_ = lean_box((v_res_3904_) as usize);
    return v_r_3905_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(
    mut v_00_u03b2_3906_: *mut LeanObject,
    mut v_m_3907_: *mut LeanObject,
    mut v_a_3908_: *mut LeanObject,
    mut v_b_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    v___x_3910_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_3907_, v_a_3908_, v_b_3909_);
    return v___x_3910_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3911_: *mut LeanObject,
    mut v_a_3912_: *mut LeanObject,
    mut v_x_3913_: *mut LeanObject,
) -> u8 {
    let mut v___x_3914_: u8 = 0;
    v___x_3914_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_3912_, v_x_3913_);
    return v___x_3914_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3915_: *mut LeanObject,
    mut v_a_3916_: *mut LeanObject,
    mut v_x_3917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3918_: u8 = 0;
    let mut v_r_3919_: *mut LeanObject = core::ptr::null_mut();
    v_res_3918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_3915_, v_a_3916_, v_x_3917_);
    lean_dec(v_x_3917_);
    lean_dec_ref(v_a_3916_);
    v_r_3919_ = lean_box((v_res_3918_) as usize);
    return v_r_3919_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(
    mut v_00_u03b2_3920_: *mut LeanObject,
    mut v_data_3921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    v___x_3922_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_data_3921_);
    return v___x_3922_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(
    mut v_00_u03b2_3923_: *mut LeanObject,
    mut v_i_3924_: *mut LeanObject,
    mut v_source_3925_: *mut LeanObject,
    mut v_target_3926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    v___x_3927_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v_i_3924_, v_source_3925_, v_target_3926_);
    return v___x_3927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(
    mut v_00_u03b2_3928_: *mut LeanObject,
    mut v_x_3929_: *mut LeanObject,
    mut v_x_3930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    v___x_3931_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_x_3929_, v_x_3930_);
    return v___x_3931_;
}
pub unsafe fn _init_l_Lake_Package_transDepsFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___x_3933_: u8 = 0;
    let mut v___f_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: u8 = 0;
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    v___x_3933_ = 1;
    v___f_3934_ = l_Lake_Package_depsFacetConfig___closed__0;
    v___x_3935_ = 0;
    v___x_3936_ = lean_box(0);
    v___x_3937_ = l_Lake_Package_transDepsFacetConfig___closed__0;
    v___x_3938_ = l_Lake_Package_keyword;
    v___x_3939_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_3939_, 0, v___x_3938_);
    lean_ctor_set(v___x_3939_, 1, v___x_3937_);
    lean_ctor_set(v___x_3939_, 2, v___x_3936_);
    lean_ctor_set(v___x_3939_, 3, v___f_3934_);
    lean_ctor_set_uint8(
        v___x_3939_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_3935_,
    );
    lean_ctor_set_uint8(
        v___x_3939_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_3933_,
    );
    return v___x_3939_;
}
pub unsafe fn _init_l_Lake_Package_transDepsFacetConfig() -> *mut LeanObject {
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    v___x_3940_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_transDepsFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Package_transDepsFacetConfig___closed__1_once),
        _init_l_Lake_Package_transDepsFacetConfig___closed__1,
    );
    return v___x_3940_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(
    mut v_self_3941_: *mut LeanObject,
    mut v_a_3942_: *mut LeanObject,
    mut v_a_3943_: *mut LeanObject,
    mut v_a_3944_: *mut LeanObject,
    mut v_a_3945_: *mut LeanObject,
    mut v_a_3946_: *mut LeanObject,
    mut v_a_3947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preferReleaseBuild_3950_: u8 = 0;
    v_config_3949_ = lean_ctor_get(v_self_3941_, 6);
    v_preferReleaseBuild_3950_ = lean_ctor_get_uint8(
        v_config_3949_,
        (core::mem::size_of::<*mut LeanObject>() * 27 + 2) as u32,
    );
    if v_preferReleaseBuild_3950_ == 0 {
        let mut v_keyName_3951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
        v_keyName_3951_ = lean_ctor_get(v_self_3941_, 2);
        v___x_3952_ = l_Lake_Package_optReservoirBarrelFacet;
        lean_inc(v_keyName_3951_);
        v___x_3953_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3953_, 0, v_keyName_3951_);
        v___x_3954_ = l_Lake_Package_keyword;
        v___x_3955_ = lean_alloc_ctor(1, 4, (0) as u32);
        lean_ctor_set(v___x_3955_, 0, v___x_3953_);
        lean_ctor_set(v___x_3955_, 1, v___x_3954_);
        lean_ctor_set(v___x_3955_, 2, v_self_3941_);
        lean_ctor_set(v___x_3955_, 3, v___x_3952_);
        lean_inc_ref(v_a_3946_);
        lean_inc(v_a_3945_);
        lean_inc(v_a_3944_);
        lean_inc(v_a_3943_);
        v___x_3956_ = lean_apply_7(
            v_a_3942_,
            v___x_3955_,
            v_a_3943_,
            v_a_3944_,
            v_a_3945_,
            v_a_3946_,
            v_a_3947_,
            lean_box(0),
        );
        return v___x_3956_;
    } else {
        let mut v_keyName_3957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
        v_keyName_3957_ = lean_ctor_get(v_self_3941_, 2);
        v___x_3958_ = l_Lake_Package_optGitHubReleaseFacet;
        lean_inc(v_keyName_3957_);
        v___x_3959_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3959_, 0, v_keyName_3957_);
        v___x_3960_ = l_Lake_Package_keyword;
        v___x_3961_ = lean_alloc_ctor(1, 4, (0) as u32);
        lean_ctor_set(v___x_3961_, 0, v___x_3959_);
        lean_ctor_set(v___x_3961_, 1, v___x_3960_);
        lean_ctor_set(v___x_3961_, 2, v_self_3941_);
        lean_ctor_set(v___x_3961_, 3, v___x_3958_);
        lean_inc_ref(v_a_3946_);
        lean_inc(v_a_3945_);
        lean_inc(v_a_3944_);
        lean_inc(v_a_3943_);
        v___x_3962_ = lean_apply_7(
            v_a_3942_,
            v___x_3961_,
            v_a_3943_,
            v_a_3944_,
            v_a_3945_,
            v_a_3946_,
            v_a_3947_,
            lean_box(0),
        );
        return v___x_3962_;
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(
    mut v_self_3963_: *mut LeanObject,
    mut v_a_3964_: *mut LeanObject,
    mut v_a_3965_: *mut LeanObject,
    mut v_a_3966_: *mut LeanObject,
    mut v_a_3967_: *mut LeanObject,
    mut v_a_3968_: *mut LeanObject,
    mut v_a_3969_: *mut LeanObject,
    mut v_a_3970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3971_: *mut LeanObject = core::ptr::null_mut();
    v_res_3971_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(
        v_self_3963_,
        v_a_3964_,
        v_a_3965_,
        v_a_3966_,
        v_a_3967_,
        v_a_3968_,
        v_a_3969_,
    );
    lean_dec_ref(v_a_3968_);
    lean_dec(v_a_3967_);
    lean_dec(v_a_3966_);
    lean_dec(v_a_3965_);
    return v_res_3971_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(
    mut v_fmt_3974_: u8,
    mut v_a_3975_: u8,
) -> *mut LeanObject {
    if v_fmt_3974_ == 0 {
        if v_a_3975_ == 0 {
            let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
            v___x_3976_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0;
            return v___x_3976_;
        } else {
            let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
            v___x_3977_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1;
            return v___x_3977_;
        }
    } else {
        let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
        v___x_3978_ = lean_alloc_ctor(1, 0, (1) as u32);
        lean_ctor_set_uint8(v___x_3978_, 0 as u32, v_a_3975_);
        v___x_3979_ = l_Lean_Json_compress(v___x_3978_);
        return v___x_3979_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(
    mut v_fmt_3980_: *mut LeanObject,
    mut v_a_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_3982_: u8 = 0;
    let mut v_a_boxed_3983_: u8 = 0;
    let mut v_res_3984_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_3982_ = (lean_unbox(v_fmt_3980_) as u8);
    v_a_boxed_3983_ = (lean_unbox(v_a_3981_) as u8);
    v_res_3984_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(
        v_fmt_boxed_3982_,
        v_a_boxed_3983_,
    );
    return v_res_3984_;
}
pub unsafe fn _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___f_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: u8 = 0;
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    v___f_3987_ = l_Lake_Package_optBuildCacheFacetConfig___closed__1;
    v___x_3988_ = 1;
    v___x_3989_ = l_Lake_instDataKindBool;
    v___f_3990_ = l_Lake_Package_optBuildCacheFacetConfig___closed__0;
    v___x_3991_ = l_Lake_Package_keyword;
    v___x_3992_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_3992_, 0, v___x_3991_);
    lean_ctor_set(v___x_3992_, 1, v___f_3990_);
    lean_ctor_set(v___x_3992_, 2, v___x_3989_);
    lean_ctor_set(v___x_3992_, 3, v___f_3987_);
    lean_ctor_set_uint8(
        v___x_3992_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_3988_,
    );
    lean_ctor_set_uint8(
        v___x_3992_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_3988_,
    );
    return v___x_3992_;
}
pub unsafe fn _init_l_Lake_Package_optBuildCacheFacetConfig() -> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    v___x_3993_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_optBuildCacheFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Package_optBuildCacheFacetConfig___closed__2_once),
        _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2,
    );
    return v___x_3993_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(
    mut v_self_3996_: *mut LeanObject,
    mut v_a_3997_: *mut LeanObject,
    mut v_a_3998_: *mut LeanObject,
    mut v_a_3999_: *mut LeanObject,
    mut v_a_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v_a_4002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4006_: u8 = 0;
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: u8 = 0;
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4030_: u8 = 0;
    let mut v___y_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4033_: u8 = 0;
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: u8 = 0;
    let mut v_toContext_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noCache_4039_: u8 = 0;
    let mut v_toolchain_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4042_: u8 = 0;
    let mut v_a_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildDir_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preferReleaseBuild_4049_: u8 = 0;
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: u8 = 0;
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: u8 = 0;
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: u8 = 0;
    let mut v___x_4057_: u8 = 0;
    let mut v___x_4058_: u8 = 0;
    let mut v___x_4059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_4037_ = lean_ctor_get(v_a_4001_, 1);
                v_lakeEnv_4038_ = lean_ctor_get(v_toContext_4037_, 0);
                v_noCache_4039_ = lean_ctor_get_uint8(
                    v_lakeEnv_4038_,
                    (core::mem::size_of::<*mut LeanObject>() * 19) as u32,
                );
                v_toolchain_4040_ = lean_ctor_get(v_lakeEnv_4038_, 18);
                if v_noCache_4039_ == 0 {
                    v___x_4058_ = 1;
                    v_a_4042_ = v___x_4058_;
                    v_a_4043_ = v_a_4002_;
                    state = 4;
                    continue;
                } else {
                    v___x_4059_ = 0;
                    v_a_4042_ = v___x_4059_;
                    v_a_4043_ = v_a_4002_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_4007_ = 1;
                v___x_4008_ = lean_box(0);
                v___x_4009_ = lean_unsigned_to_nat(0);
                v___x_4010_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0;
                v___x_4011_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                v___x_4012_ = 0;
                v___x_4013_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                v___x_4014_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_4014_, 0, v___x_4010_);
                lean_ctor_set(v___x_4014_, 1, v___x_4013_);
                lean_ctor_set(v___x_4014_, 2, v___x_4009_);
                lean_ctor_set_uint8(
                    v___x_4014_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4012_,
                );
                lean_ctor_set_uint8(
                    v___x_4014_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___y_4006_,
                );
                v___x_4015_ = lean_box((v___x_4007_) as usize);
                v___x_4016_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4016_, 0, v___x_4015_);
                lean_ctor_set(v___x_4016_, 1, v___x_4014_);
                v___x_4017_ = lean_task_pure(v___x_4016_);
                v___x_4018_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_4018_, 0, v___x_4017_);
                lean_ctor_set(v___x_4018_, 1, v___x_4008_);
                lean_ctor_set(v___x_4018_, 2, v___x_4011_);
                lean_ctor_set_uint8(
                    v___x_4018_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___y_4006_,
                );
                v___x_4019_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4019_, 0, v___x_4018_);
                lean_ctor_set(v___x_4019_, 1, v___y_4005_);
                return v___x_4019_;
            }
            2 => {
                v___x_4023_ = l_Lake_Package_optBuildCacheFacet;
                v___x_4024_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4024_, 0, v___y_4021_);
                v___x_4025_ = l_Lake_Package_keyword;
                v___x_4026_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_4026_, 0, v___x_4024_);
                lean_ctor_set(v___x_4026_, 1, v___x_4025_);
                lean_ctor_set(v___x_4026_, 2, v_self_3996_);
                lean_ctor_set(v___x_4026_, 3, v___x_4023_);
                lean_inc_ref(v_a_4001_);
                lean_inc(v_a_4000_);
                lean_inc(v_a_3999_);
                lean_inc(v_a_3998_);
                v___x_4027_ = lean_apply_7(
                    v_a_3997_,
                    v___x_4026_,
                    v_a_3998_,
                    v_a_3999_,
                    v_a_4000_,
                    v_a_4001_,
                    v___y_4022_,
                    lean_box(0),
                );
                return v___x_4027_;
            }
            3 => {
                if v___y_4033_ == 0 {
                    lean_dec(v___y_4031_);
                    lean_dec_ref(v_a_3997_);
                    lean_dec_ref(v_self_3996_);
                    v___y_4005_ = v___y_4032_;
                    v___y_4006_ = v___y_4033_;
                    state = 1;
                    continue;
                } else {
                    v___x_4034_ = lean_string_utf8_byte_size(v___y_4029_);
                    v___x_4035_ = lean_unsigned_to_nat(0);
                    v___x_4036_ = lean_nat_dec_eq(v___x_4034_, v___x_4035_);
                    if v___x_4036_ == 0 {
                        v___y_4021_ = v___y_4031_;
                        v___y_4022_ = v___y_4032_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___y_4031_);
                        lean_dec_ref(v_a_3997_);
                        lean_dec_ref(v_self_3996_);
                        v___y_4005_ = v___y_4032_;
                        v___y_4006_ = v___y_4030_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                v_config_4044_ = lean_ctor_get(v_self_3996_, 6);
                v_keyName_4045_ = lean_ctor_get(v_self_3996_, 2);
                v_dir_4046_ = lean_ctor_get(v_self_3996_, 4);
                v_scope_4047_ = lean_ctor_get(v_self_3996_, 10);
                v_buildDir_4048_ = lean_ctor_get(v_config_4044_, 5);
                v_preferReleaseBuild_4049_ = lean_ctor_get_uint8(
                    v_config_4044_,
                    (core::mem::size_of::<*mut LeanObject>() * 27 + 2) as u32,
                );
                lean_inc_ref(v_buildDir_4048_);
                v___x_4050_ = l_System_FilePath_normalize(v_buildDir_4048_);
                lean_inc_ref(v_dir_4046_);
                v___x_4051_ = l_Lake_joinRelative(v_dir_4046_, v___x_4050_);
                v___x_4052_ = l_System_FilePath_pathExists(v___x_4051_);
                lean_dec_ref(v___x_4051_);
                if v_a_4042_ == 0 {
                    lean_dec_ref(v_a_3997_);
                    lean_dec_ref(v_self_3996_);
                    v___y_4005_ = v_a_4043_;
                    v___y_4006_ = v_a_4042_;
                    state = 1;
                    continue;
                } else {
                    if v___x_4052_ == 0 {
                        if v_preferReleaseBuild_4049_ == 0 {
                            v___x_4053_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0;
                            v___x_4054_ = lean_string_dec_eq(v_scope_4047_, v___x_4053_);
                            if v___x_4054_ == 0 {
                                v___x_4055_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1;
                                v___x_4056_ = lean_string_dec_eq(v_scope_4047_, v___x_4055_);
                                lean_inc(v_keyName_4045_);
                                v___y_4029_ = v_toolchain_4040_;
                                v___y_4030_ = v_preferReleaseBuild_4049_;
                                v___y_4031_ = v_keyName_4045_;
                                v___y_4032_ = v_a_4043_;
                                v___y_4033_ = v___x_4056_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_keyName_4045_);
                                v___y_4029_ = v_toolchain_4040_;
                                v___y_4030_ = v_preferReleaseBuild_4049_;
                                v___y_4031_ = v_keyName_4045_;
                                v___y_4032_ = v_a_4043_;
                                v___y_4033_ = v___x_4054_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_inc(v_keyName_4045_);
                            v___y_4021_ = v_keyName_4045_;
                            v___y_4022_ = v_a_4043_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_3997_);
                        lean_dec_ref(v_self_3996_);
                        v___x_4057_ = 0;
                        v___y_4005_ = v_a_4043_;
                        v___y_4006_ = v___x_4057_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(
    mut v_self_4060_: *mut LeanObject,
    mut v_a_4061_: *mut LeanObject,
    mut v_a_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
    mut v_a_4064_: *mut LeanObject,
    mut v_a_4065_: *mut LeanObject,
    mut v_a_4066_: *mut LeanObject,
    mut v_a_4067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4068_: *mut LeanObject = core::ptr::null_mut();
    v_res_4068_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(
        v_self_4060_,
        v_a_4061_,
        v_a_4062_,
        v_a_4063_,
        v_a_4064_,
        v_a_4065_,
        v_a_4066_,
    );
    lean_dec_ref(v_a_4065_);
    lean_dec(v_a_4064_);
    lean_dec(v_a_4063_);
    lean_dec(v_a_4062_);
    return v_res_4068_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(
    mut v_self_4073_: *mut LeanObject,
    mut v_facet_4074_: *mut LeanObject,
    mut v_a_4075_: *mut LeanObject,
    mut v_a_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBuildConfig_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_4079_: u8 = 0;
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: u8 = 0;
    v_toBuildConfig_4078_ = lean_ctor_get(v_a_4075_, 0);
    v_verbosity_4079_ = lean_ctor_get_uint8(
        v_toBuildConfig_4078_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
    );
    v___x_4080_ = 2;
    v___x_4081_ = l_Lake_instDecidableEqVerbosity(v_verbosity_4079_, v___x_4080_);
    if v___x_4081_ == 0 {
        let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_facet_4074_);
        lean_dec_ref(v_self_4073_);
        v___x_4082_ =
            l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
        v___x_4083_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4083_, 0, v___x_4082_);
        lean_ctor_set(v___x_4083_, 1, v_a_4076_);
        return v___x_4083_;
    } else {
        let mut v_baseName_4084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
        v_baseName_4084_ = lean_ctor_get(v_self_4073_, 1);
        lean_inc(v_baseName_4084_);
        lean_dec_ref(v_self_4073_);
        v___x_4085_ =
            l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
        v___x_4086_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_baseName_4084_,
            v___x_4081_,
        );
        v___x_4087_ = lean_string_append(v___x_4085_, v___x_4086_);
        lean_dec_ref(v___x_4086_);
        v___x_4088_ =
            l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
        v___x_4089_ = lean_string_append(v___x_4087_, v___x_4088_);
        v___x_4090_ = l_Lake_Name_eraseHead(v_facet_4074_);
        v___x_4091_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v___x_4090_,
            v___x_4081_,
        );
        v___x_4092_ = lean_string_append(v___x_4089_, v___x_4091_);
        lean_dec_ref(v___x_4091_);
        v___x_4093_ =
            l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
        v___x_4094_ = lean_string_append(v___x_4092_, v___x_4093_);
        v___x_4095_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4095_, 0, v___x_4094_);
        lean_ctor_set(v___x_4095_, 1, v_a_4076_);
        return v___x_4095_;
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(
    mut v_self_4096_: *mut LeanObject,
    mut v_facet_4097_: *mut LeanObject,
    mut v_a_4098_: *mut LeanObject,
    mut v_a_4099_: *mut LeanObject,
    mut v_a_4100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4101_: *mut LeanObject = core::ptr::null_mut();
    v_res_4101_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(
        v_self_4096_,
        v_facet_4097_,
        v_a_4098_,
        v_a_4099_,
    );
    lean_dec_ref(v_a_4098_);
    return v_res_4101_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(
    mut v_self_4102_: *mut LeanObject,
    mut v_facet_4103_: *mut LeanObject,
    mut v_a_4104_: *mut LeanObject,
    mut v_a_4105_: *mut LeanObject,
    mut v_a_4106_: *mut LeanObject,
    mut v_a_4107_: *mut LeanObject,
    mut v_a_4108_: *mut LeanObject,
    mut v_a_4109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBuildConfig_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_4112_: u8 = 0;
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: u8 = 0;
    v_toBuildConfig_4111_ = lean_ctor_get(v_a_4108_, 0);
    v_verbosity_4112_ = lean_ctor_get_uint8(
        v_toBuildConfig_4111_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
    );
    v___x_4113_ = 2;
    v___x_4114_ = l_Lake_instDecidableEqVerbosity(v_verbosity_4112_, v___x_4113_);
    if v___x_4114_ == 0 {
        let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_facet_4103_);
        lean_dec_ref(v_self_4102_);
        v___x_4115_ =
            l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
        v___x_4116_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4116_, 0, v___x_4115_);
        lean_ctor_set(v___x_4116_, 1, v_a_4109_);
        return v___x_4116_;
    } else {
        let mut v_baseName_4117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
        v_baseName_4117_ = lean_ctor_get(v_self_4102_, 1);
        lean_inc(v_baseName_4117_);
        lean_dec_ref(v_self_4102_);
        v___x_4118_ =
            l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
        v___x_4119_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_baseName_4117_,
            v___x_4114_,
        );
        v___x_4120_ = lean_string_append(v___x_4118_, v___x_4119_);
        lean_dec_ref(v___x_4119_);
        v___x_4121_ =
            l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
        v___x_4122_ = lean_string_append(v___x_4120_, v___x_4121_);
        v___x_4123_ = l_Lake_Name_eraseHead(v_facet_4103_);
        v___x_4124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v___x_4123_,
            v___x_4114_,
        );
        v___x_4125_ = lean_string_append(v___x_4122_, v___x_4124_);
        lean_dec_ref(v___x_4124_);
        v___x_4126_ =
            l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
        v___x_4127_ = lean_string_append(v___x_4125_, v___x_4126_);
        v___x_4128_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4128_, 0, v___x_4127_);
        lean_ctor_set(v___x_4128_, 1, v_a_4109_);
        return v___x_4128_;
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(
    mut v_self_4129_: *mut LeanObject,
    mut v_facet_4130_: *mut LeanObject,
    mut v_a_4131_: *mut LeanObject,
    mut v_a_4132_: *mut LeanObject,
    mut v_a_4133_: *mut LeanObject,
    mut v_a_4134_: *mut LeanObject,
    mut v_a_4135_: *mut LeanObject,
    mut v_a_4136_: *mut LeanObject,
    mut v_a_4137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4138_: *mut LeanObject = core::ptr::null_mut();
    v_res_4138_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(
        v_self_4129_,
        v_facet_4130_,
        v_a_4131_,
        v_a_4132_,
        v_a_4133_,
        v_a_4134_,
        v_a_4135_,
        v_a_4136_,
    );
    lean_dec_ref(v_a_4135_);
    lean_dec(v_a_4134_);
    lean_dec(v_a_4133_);
    lean_dec(v_a_4132_);
    lean_dec_ref(v_a_4131_);
    return v_res_4138_;
}
pub unsafe fn _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    v___x_4141_ = l_Lake_Package_optReservoirBarrelFacet;
    v___x_4142_ = l_Lake_Name_eraseHead(v___x_4141_);
    return v___x_4142_;
}
pub unsafe fn _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    v___x_4143_ = l_Lake_Package_optGitHubReleaseFacet;
    v___x_4144_ = l_Lake_Name_eraseHead(v___x_4143_);
    return v___x_4144_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(
    mut v_self_4145_: *mut LeanObject,
    mut v_success_4146_: u8,
    mut v___y_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4158_: u8 = 0;
    let mut v_wantsRebuild_4159_: u8 = 0;
    let mut v_trace_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: u8 = 0;
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut v_a_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4180_: u8 = 0;
    let mut v_wantsRebuild_4181_: u8 = 0;
    let mut v_trace_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut v_config_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preferReleaseBuild_4199_: u8 = 0;
    let mut v_toBuildConfig_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_4202_: u8 = 0;
    let mut v___x_4203_: u8 = 0;
    let mut v___x_4204_: u8 = 0;
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBuildConfig_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_4218_: u8 = 0;
    let mut v___x_4219_: u8 = 0;
    let mut v___x_4220_: u8 = 0;
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_success_4146_ == 0 {
                    v_config_4198_ = lean_ctor_get(v_self_4145_, 6);
                    v_preferReleaseBuild_4199_ = lean_ctor_get_uint8(
                        v_config_4198_,
                        (core::mem::size_of::<*mut LeanObject>() * 27 + 2) as u32,
                    );
                    if v_preferReleaseBuild_4199_ == 0 {
                        v_toBuildConfig_4200_ = lean_ctor_get(v___y_4151_, 0);
                        v_baseName_4201_ = lean_ctor_get(v_self_4145_, 1);
                        lean_inc(v_baseName_4201_);
                        lean_dec_ref(v_self_4145_);
                        v_verbosity_4202_ = lean_ctor_get_uint8(
                            v_toBuildConfig_4200_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        );
                        v___x_4203_ = 2;
                        v___x_4204_ =
                            l_Lake_instDecidableEqVerbosity(v_verbosity_4202_, v___x_4203_);
                        if v___x_4204_ == 0 {
                            lean_dec(v_baseName_4201_);
                            v___x_4205_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
                            v_a_4155_ = v___x_4205_;
                            v_a_4156_ = v___y_4152_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4206_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
                            v___x_4207_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_baseName_4201_,
                                    v___x_4204_,
                                );
                            v___x_4208_ = lean_string_append(v___x_4206_, v___x_4207_);
                            lean_dec_ref(v___x_4207_);
                            v___x_4209_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                            v___x_4210_ = lean_string_append(v___x_4208_, v___x_4209_);
                            v___x_4211_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once), _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
                            v___x_4212_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_4211_,
                                    v___x_4204_,
                                );
                            v___x_4213_ = lean_string_append(v___x_4210_, v___x_4212_);
                            lean_dec_ref(v___x_4212_);
                            v___x_4214_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
                            v___x_4215_ = lean_string_append(v___x_4213_, v___x_4214_);
                            v_a_4155_ = v___x_4215_;
                            v_a_4156_ = v___y_4152_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_toBuildConfig_4216_ = lean_ctor_get(v___y_4151_, 0);
                        v_baseName_4217_ = lean_ctor_get(v_self_4145_, 1);
                        lean_inc(v_baseName_4217_);
                        lean_dec_ref(v_self_4145_);
                        v_verbosity_4218_ = lean_ctor_get_uint8(
                            v_toBuildConfig_4216_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                        );
                        v___x_4219_ = 2;
                        v___x_4220_ =
                            l_Lake_instDecidableEqVerbosity(v_verbosity_4218_, v___x_4219_);
                        if v___x_4220_ == 0 {
                            lean_dec(v_baseName_4217_);
                            v___x_4221_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
                            v_a_4177_ = v___x_4221_;
                            v_a_4178_ = v___y_4152_;
                            state = 4;
                            continue;
                        } else {
                            v___x_4222_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
                            v___x_4223_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_baseName_4217_,
                                    v___x_4220_,
                                );
                            v___x_4224_ = lean_string_append(v___x_4222_, v___x_4223_);
                            lean_dec_ref(v___x_4223_);
                            v___x_4225_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                            v___x_4226_ = lean_string_append(v___x_4224_, v___x_4225_);
                            v___x_4227_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
                            v___x_4228_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_4227_,
                                    v___x_4220_,
                                );
                            v___x_4229_ = lean_string_append(v___x_4226_, v___x_4228_);
                            lean_dec_ref(v___x_4228_);
                            v___x_4230_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
                            v___x_4231_ = lean_string_append(v___x_4229_, v___x_4230_);
                            v_a_4177_ = v___x_4231_;
                            v_a_4178_ = v___y_4152_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_self_4145_);
                    v___x_4232_ = lean_box(0);
                    v___x_4233_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4233_, 0, v___x_4232_);
                    lean_ctor_set(v___x_4233_, 1, v___y_4152_);
                    return v___x_4233_;
                }
            }
            1 => {
                v_log_4157_ = lean_ctor_get(v_a_4156_, 0);
                v_action_4158_ = lean_ctor_get_uint8(
                    v_a_4156_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4159_ = lean_ctor_get_uint8(
                    v_a_4156_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4160_ = lean_ctor_get(v_a_4156_, 1);
                v_buildTime_4161_ = lean_ctor_get(v_a_4156_, 2);
                v_isSharedCheck_4175_ = (!lean_is_exclusive(v_a_4156_)) as u8;
                if v_isSharedCheck_4175_ == 0 {
                    v___x_4163_ = v_a_4156_;
                    v_isShared_4164_ = v_isSharedCheck_4175_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_buildTime_4161_);
                    lean_inc(v_trace_4160_);
                    lean_inc(v_log_4157_);
                    lean_dec(v_a_4156_);
                    v___x_4163_ = lean_box(0);
                    v_isShared_4164_ = v_isSharedCheck_4175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4165_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0;
                v___x_4166_ = lean_string_append(v___x_4165_, v_a_4155_);
                lean_dec_ref(v_a_4155_);
                v___x_4167_ = 0;
                v___x_4168_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4168_, 0, v___x_4166_);
                lean_ctor_set_uint8(
                    v___x_4168_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4167_,
                );
                v___x_4169_ = lean_box(0);
                v___x_4170_ = lean_array_push(v_log_4157_, v___x_4168_);
                if v_isShared_4164_ == 0 {
                    lean_ctor_set(v___x_4163_, 0, v___x_4170_);
                    v___x_4172_ = v___x_4163_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4170_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 1, v_trace_4160_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 2, v_buildTime_4161_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4174_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4158_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4174_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4159_,
                    );
                    v___x_4172_ = v_reuseFailAlloc_4174_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4173_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4173_, 0, v___x_4169_);
                lean_ctor_set(v___x_4173_, 1, v___x_4172_);
                return v___x_4173_;
            }
            4 => {
                v_log_4179_ = lean_ctor_get(v_a_4178_, 0);
                v_action_4180_ = lean_ctor_get_uint8(
                    v_a_4178_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4181_ = lean_ctor_get_uint8(
                    v_a_4178_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4182_ = lean_ctor_get(v_a_4178_, 1);
                v_buildTime_4183_ = lean_ctor_get(v_a_4178_, 2);
                v_isSharedCheck_4197_ = (!lean_is_exclusive(v_a_4178_)) as u8;
                if v_isSharedCheck_4197_ == 0 {
                    v___x_4185_ = v_a_4178_;
                    v_isShared_4186_ = v_isSharedCheck_4197_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_buildTime_4183_);
                    lean_inc(v_trace_4182_);
                    lean_inc(v_log_4179_);
                    lean_dec(v_a_4178_);
                    v___x_4185_ = lean_box(0);
                    v_isShared_4186_ = v_isSharedCheck_4197_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4187_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1;
                v___x_4188_ = lean_string_append(v___x_4187_, v_a_4177_);
                lean_dec_ref(v_a_4177_);
                v___x_4189_ = 2;
                v___x_4190_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4190_, 0, v___x_4188_);
                lean_ctor_set_uint8(
                    v___x_4190_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4189_,
                );
                v___x_4191_ = lean_box(0);
                v___x_4192_ = lean_array_push(v_log_4179_, v___x_4190_);
                if v_isShared_4186_ == 0 {
                    lean_ctor_set(v___x_4185_, 0, v___x_4192_);
                    v___x_4194_ = v___x_4185_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4192_);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_trace_4182_);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 2, v_buildTime_4183_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4196_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4180_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4196_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4181_,
                    );
                    v___x_4194_ = v_reuseFailAlloc_4196_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4195_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4195_, 0, v___x_4191_);
                lean_ctor_set(v___x_4195_, 1, v___x_4194_);
                return v___x_4195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(
    mut v_self_4234_: *mut LeanObject,
    mut v_success_4235_: *mut LeanObject,
    mut v___y_4236_: *mut LeanObject,
    mut v___y_4237_: *mut LeanObject,
    mut v___y_4238_: *mut LeanObject,
    mut v___y_4239_: *mut LeanObject,
    mut v___y_4240_: *mut LeanObject,
    mut v___y_4241_: *mut LeanObject,
    mut v___y_4242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_success_boxed_4243_: u8 = 0;
    let mut v_res_4244_: *mut LeanObject = core::ptr::null_mut();
    v_success_boxed_4243_ = (lean_unbox(v_success_4235_) as u8);
    v_res_4244_ =
        l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(
            v_self_4234_,
            v_success_boxed_4243_,
            v___y_4236_,
            v___y_4237_,
            v___y_4238_,
            v___y_4239_,
            v___y_4240_,
            v___y_4241_,
        );
    lean_dec_ref(v___y_4240_);
    lean_dec(v___y_4239_);
    lean_dec(v___y_4238_);
    lean_dec(v___y_4237_);
    lean_dec_ref(v___y_4236_);
    return v_res_4244_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(
    mut v_self_4245_: *mut LeanObject,
    mut v_a_4246_: *mut LeanObject,
    mut v_a_4247_: *mut LeanObject,
    mut v_a_4248_: *mut LeanObject,
    mut v_a_4249_: *mut LeanObject,
    mut v_a_4250_: *mut LeanObject,
    mut v_a_4251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v___f_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: u8 = 0;
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4268_: u8 = 0;
    let mut v_a_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_4246_);
                lean_inc_ref(v_self_4245_);
                v___x_4253_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(
                    v_self_4245_,
                    v_a_4246_,
                    v_a_4247_,
                    v_a_4248_,
                    v_a_4249_,
                    v_a_4250_,
                    v_a_4251_,
                );
                if lean_obj_tag(v___x_4253_) == 0 {
                    v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
                    v_a_4255_ = lean_ctor_get(v___x_4253_, 1);
                    v_isSharedCheck_4268_ = (!lean_is_exclusive(v___x_4253_)) as u8;
                    if v_isSharedCheck_4268_ == 0 {
                        v___x_4257_ = v___x_4253_;
                        v_isShared_4258_ = v_isSharedCheck_4268_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4255_);
                        lean_inc(v_a_4254_);
                        lean_dec(v___x_4253_);
                        v___x_4257_ = lean_box(0);
                        v_isShared_4258_ = v_isSharedCheck_4268_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_4246_);
                    lean_dec_ref(v_self_4245_);
                    v_a_4269_ = lean_ctor_get(v___x_4253_, 0);
                    v_a_4270_ = lean_ctor_get(v___x_4253_, 1);
                    v_isSharedCheck_4277_ = (!lean_is_exclusive(v___x_4253_)) as u8;
                    if v_isSharedCheck_4277_ == 0 {
                        v___x_4272_ = v___x_4253_;
                        v_isShared_4273_ = v_isSharedCheck_4277_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4270_);
                        lean_inc(v_a_4269_);
                        lean_dec(v___x_4253_);
                        v___x_4272_ = lean_box(0);
                        v_isShared_4273_ = v_isSharedCheck_4277_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_4259_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                lean_closure_set(v___f_4259_, 0, v_self_4245_);
                v___x_4260_ = l_Lake_instDataKindUnit;
                v___x_4261_ = lean_unsigned_to_nat(0);
                v___x_4262_ = 0;
                v___x_4263_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                v___x_4264_ = l_Lake_Job_mapM___redArg(
                    v___x_4260_,
                    v_a_4254_,
                    v___f_4259_,
                    v___x_4261_,
                    v___x_4262_,
                    v_a_4246_,
                    v_a_4247_,
                    v_a_4248_,
                    v_a_4249_,
                    v_a_4250_,
                    v___x_4263_,
                );
                if v_isShared_4258_ == 0 {
                    lean_ctor_set(v___x_4257_, 0, v___x_4264_);
                    v___x_4266_ = v___x_4257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
                    lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_a_4255_);
                    v___x_4266_ = v_reuseFailAlloc_4267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4266_;
            }
            3 => {
                if v_isShared_4273_ == 0 {
                    v___x_4275_ = v___x_4272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4269_);
                    lean_ctor_set(v_reuseFailAlloc_4276_, 1, v_a_4270_);
                    v___x_4275_ = v_reuseFailAlloc_4276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(
    mut v_self_4278_: *mut LeanObject,
    mut v_a_4279_: *mut LeanObject,
    mut v_a_4280_: *mut LeanObject,
    mut v_a_4281_: *mut LeanObject,
    mut v_a_4282_: *mut LeanObject,
    mut v_a_4283_: *mut LeanObject,
    mut v_a_4284_: *mut LeanObject,
    mut v_a_4285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4286_: *mut LeanObject = core::ptr::null_mut();
    v_res_4286_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(
        v_self_4278_,
        v_a_4279_,
        v_a_4280_,
        v_a_4281_,
        v_a_4282_,
        v_a_4283_,
        v_a_4284_,
    );
    lean_dec_ref(v_a_4283_);
    lean_dec(v_a_4282_);
    lean_dec(v_a_4281_);
    lean_dec(v_a_4280_);
    return v_res_4286_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(
    mut v_self_4287_: *mut LeanObject,
    mut v_as_4288_: *mut LeanObject,
    mut v_sz_4289_: usize,
    mut v_i_4290_: usize,
    mut v_b_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
    mut v___y_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4299_: u8 = 0;
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: usize = 0;
    let mut v___x_4307_: usize = 0;
    let mut v_a_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4313_: u8 = 0;
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4299_ = lean_usize_dec_lt(v_i_4290_, v_sz_4289_);
                if v___x_4299_ == 0 {
                    lean_dec_ref(v___y_4292_);
                    lean_dec_ref(v_self_4287_);
                    v___x_4300_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4300_, 0, v_b_4291_);
                    lean_ctor_set(v___x_4300_, 1, v___y_4297_);
                    return v___x_4300_;
                } else {
                    v_a_4301_ = lean_array_uget_borrowed(v_as_4288_, v_i_4290_);
                    lean_inc_ref(v___y_4292_);
                    lean_inc(v_a_4301_);
                    lean_inc_ref(v_self_4287_);
                    v___x_4302_ = l_Lake_Package_fetchTargetJob(
                        v_self_4287_,
                        v_a_4301_,
                        v___y_4292_,
                        v___y_4293_,
                        v___y_4294_,
                        v___y_4295_,
                        v___y_4296_,
                        v___y_4297_,
                    );
                    if lean_obj_tag(v___x_4302_) == 0 {
                        v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
                        lean_inc(v_a_4303_);
                        v_a_4304_ = lean_ctor_get(v___x_4302_, 1);
                        lean_inc(v_a_4304_);
                        lean_dec_ref_known(v___x_4302_, 2);
                        v___x_4305_ = l_Lake_Job_mix___redArg(v_b_4291_, v_a_4303_);
                        v___x_4306_ = 1usize;
                        v___x_4307_ = lean_usize_add(v_i_4290_, v___x_4306_);
                        v_i_4290_ = v___x_4307_;
                        v_b_4291_ = v___x_4305_;
                        v___y_4297_ = v_a_4304_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___y_4292_);
                        lean_dec_ref(v_b_4291_);
                        lean_dec_ref(v_self_4287_);
                        v_a_4309_ = lean_ctor_get(v___x_4302_, 0);
                        v_a_4310_ = lean_ctor_get(v___x_4302_, 1);
                        v_isSharedCheck_4317_ = (!lean_is_exclusive(v___x_4302_)) as u8;
                        if v_isSharedCheck_4317_ == 0 {
                            v___x_4312_ = v___x_4302_;
                            v_isShared_4313_ = v_isSharedCheck_4317_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4310_);
                            lean_inc(v_a_4309_);
                            lean_dec(v___x_4302_);
                            v___x_4312_ = lean_box(0);
                            v_isShared_4313_ = v_isSharedCheck_4317_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4313_ == 0 {
                    v___x_4315_ = v___x_4312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4309_);
                    lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_a_4310_);
                    v___x_4315_ = v_reuseFailAlloc_4316_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(
    mut v_self_4318_: *mut LeanObject,
    mut v_as_4319_: *mut LeanObject,
    mut v_sz_4320_: *mut LeanObject,
    mut v_i_4321_: *mut LeanObject,
    mut v_b_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4330_: usize = 0;
    let mut v_i_boxed_4331_: usize = 0;
    let mut v_res_4332_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4330_ = lean_unbox_usize(v_sz_4320_);
    lean_dec(v_sz_4320_);
    v_i_boxed_4331_ = lean_unbox_usize(v_i_4321_);
    lean_dec(v_i_4321_);
    v_res_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_4318_, v_as_4319_, v_sz_boxed_4330_, v_i_boxed_4331_, v_b_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
    lean_dec_ref(v___y_4327_);
    lean_dec(v___y_4326_);
    lean_dec(v___y_4325_);
    lean_dec(v___y_4324_);
    lean_dec_ref(v_as_4319_);
    return v_res_4332_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(
    mut v_config_4333_: *mut LeanObject,
    mut v_self_4334_: *mut LeanObject,
    mut v_____r_4335_: *mut LeanObject,
    mut v_job_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_extraDepTargets_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4345_: usize = 0;
    let mut v___x_4346_: usize = 0;
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    v_extraDepTargets_4344_ = lean_ctor_get(v_config_4333_, 2);
    v_sz_4345_ = lean_array_size(v_extraDepTargets_4344_);
    v___x_4346_ = 0usize;
    v___x_4347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_4334_, v_extraDepTargets_4344_, v_sz_4345_, v___x_4346_, v_job_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
    return v___x_4347_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(
    mut v_config_4348_: *mut LeanObject,
    mut v_self_4349_: *mut LeanObject,
    mut v_____r_4350_: *mut LeanObject,
    mut v_job_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4359_: *mut LeanObject = core::ptr::null_mut();
    v_res_4359_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(
        v_config_4348_,
        v_self_4349_,
        v_____r_4350_,
        v_job_4351_,
        v___y_4352_,
        v___y_4353_,
        v___y_4354_,
        v___y_4355_,
        v___y_4356_,
        v___y_4357_,
    );
    lean_dec_ref(v___y_4356_);
    lean_dec(v___y_4355_);
    lean_dec(v___y_4354_);
    lean_dec(v___y_4353_);
    lean_dec_ref(v_config_4348_);
    return v_res_4359_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(
    mut v___x_4360_: u8,
    mut v_self_4361_: *mut LeanObject,
    mut v_job_4362_: *mut LeanObject,
    mut v___f_4363_: *mut LeanObject,
    mut v___x_4364_: *mut LeanObject,
    mut v___y_4365_: *mut LeanObject,
    mut v___y_4366_: *mut LeanObject,
    mut v___y_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
) -> *mut LeanObject {
    if v___x_4360_ == 0 {
        let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v___y_4365_);
        v___x_4372_ =
            l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(
                v_self_4361_,
                v___y_4365_,
                v___y_4366_,
                v___y_4367_,
                v___y_4368_,
                v___y_4369_,
                v___y_4370_,
            );
        if lean_obj_tag(v___x_4372_) == 0 {
            let mut v_a_4373_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_4374_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
            v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
            lean_inc(v_a_4373_);
            v_a_4374_ = lean_ctor_get(v___x_4372_, 1);
            lean_inc(v_a_4374_);
            lean_dec_ref_known(v___x_4372_, 2);
            v___x_4375_ = l_Lake_Job_add___redArg(v_job_4362_, v_a_4373_);
            lean_inc_ref(v___y_4369_);
            lean_inc(v___y_4368_);
            lean_inc(v___y_4367_);
            lean_inc(v___y_4366_);
            v___x_4376_ = lean_apply_9(
                v___f_4363_,
                v___x_4364_,
                v___x_4375_,
                v___y_4365_,
                v___y_4366_,
                v___y_4367_,
                v___y_4368_,
                v___y_4369_,
                v_a_4374_,
                lean_box(0),
            );
            return v___x_4376_;
        } else {
            lean_dec_ref(v___y_4365_);
            lean_dec_ref(v___f_4363_);
            lean_dec_ref(v_job_4362_);
            return v___x_4372_;
        }
    } else {
        let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_self_4361_);
        lean_inc_ref(v___y_4369_);
        lean_inc(v___y_4368_);
        lean_inc(v___y_4367_);
        lean_inc(v___y_4366_);
        v___x_4377_ = lean_apply_9(
            v___f_4363_,
            v___x_4364_,
            v_job_4362_,
            v___y_4365_,
            v___y_4366_,
            v___y_4367_,
            v___y_4368_,
            v___y_4369_,
            v___y_4370_,
            lean_box(0),
        );
        return v___x_4377_;
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(
    mut v___x_4378_: *mut LeanObject,
    mut v_self_4379_: *mut LeanObject,
    mut v_job_4380_: *mut LeanObject,
    mut v___f_4381_: *mut LeanObject,
    mut v___x_4382_: *mut LeanObject,
    mut v___y_4383_: *mut LeanObject,
    mut v___y_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
    mut v___y_4387_: *mut LeanObject,
    mut v___y_4388_: *mut LeanObject,
    mut v___y_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4162__boxed_4390_: u8 = 0;
    let mut v_res_4391_: *mut LeanObject = core::ptr::null_mut();
    v___x_4162__boxed_4390_ = (lean_unbox(v___x_4378_) as u8);
    v_res_4391_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(
        v___x_4162__boxed_4390_,
        v_self_4379_,
        v_job_4380_,
        v___f_4381_,
        v___x_4382_,
        v___y_4383_,
        v___y_4384_,
        v___y_4385_,
        v___y_4386_,
        v___y_4387_,
        v___y_4388_,
    );
    lean_dec_ref(v___y_4387_);
    lean_dec(v___y_4386_);
    lean_dec(v___y_4385_);
    lean_dec(v___y_4384_);
    return v_res_4391_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(
    mut v_self_4394_: *mut LeanObject,
    mut v_a_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
    mut v_a_4398_: *mut LeanObject,
    mut v_a_4399_: *mut LeanObject,
    mut v_a_4400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_wsIdx_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v___x_4418_: u8 = 0;
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: u8 = 0;
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v_task_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v_registeredJobs_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4452_: u8 = 0;
    let mut v_unused_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_wsIdx_4402_ = lean_ctor_get(v_self_4394_, 0);
                v_baseName_4403_ = lean_ctor_get(v_self_4394_, 1);
                v_config_4404_ = lean_ctor_get(v_self_4394_, 6);
                lean_inc_ref(v_self_4394_);
                lean_inc_ref(v_config_4404_);
                v___f_4405_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
                lean_closure_set(v___f_4405_, 0, v_config_4404_);
                lean_closure_set(v___f_4405_, 1, v_self_4394_);
                v___x_4406_ = l_Lake_instDataKindUnit;
                v___x_4407_ = 1;
                lean_inc(v_baseName_4403_);
                v___x_4408_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_4403_,
                    v___x_4407_,
                );
                v___x_4409_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0;
                v___x_4410_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1;
                v___x_4411_ = lean_string_append(v___x_4410_, v___x_4408_);
                v___x_4412_ = lean_string_append(v___x_4411_, v___x_4409_);
                v___x_4413_ = lean_box(0);
                v___x_4414_ = lean_box(0);
                v___x_4415_ = lean_unsigned_to_nat(0);
                v___x_4416_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0;
                v___x_4417_ = 0;
                v___x_4418_ = 0;
                v___x_4419_ = l_Lake_BuildTrace_nil(v___x_4412_);
                v___x_4420_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_4420_, 0, v___x_4416_);
                lean_ctor_set(v___x_4420_, 1, v___x_4419_);
                lean_ctor_set(v___x_4420_, 2, v___x_4415_);
                lean_ctor_set_uint8(
                    v___x_4420_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4417_,
                );
                lean_ctor_set_uint8(
                    v___x_4420_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_4418_,
                );
                v___x_4421_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4421_, 0, v___x_4413_);
                lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                v___x_4422_ = lean_task_pure(v___x_4421_);
                v___x_4423_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                v_job_4424_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v_job_4424_, 0, v___x_4422_);
                lean_ctor_set(v_job_4424_, 1, v___x_4414_);
                lean_ctor_set(v_job_4424_, 2, v___x_4423_);
                lean_ctor_set_uint8(
                    v_job_4424_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4418_,
                );
                v___x_4425_ = lean_nat_dec_eq(v_wsIdx_4402_, v___x_4415_);
                v___x_4426_ = lean_box((v___x_4425_) as usize);
                v___y_4427_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed as *mut core::ffi::c_void, 12, 5);
                lean_closure_set(v___y_4427_, 0, v___x_4426_);
                lean_closure_set(v___y_4427_, 1, v_self_4394_);
                lean_closure_set(v___y_4427_, 2, v_job_4424_);
                lean_closure_set(v___y_4427_, 3, v___f_4405_);
                lean_closure_set(v___y_4427_, 4, v___x_4413_);
                v___x_4428_ = l_Lake_ensureJob___redArg(
                    v___x_4406_,
                    v___y_4427_,
                    v_a_4395_,
                    v_a_4396_,
                    v_a_4397_,
                    v_a_4398_,
                    v_a_4399_,
                    v_a_4400_,
                );
                if lean_obj_tag(v___x_4428_) == 0 {
                    v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
                    v_a_4430_ = lean_ctor_get(v___x_4428_, 1);
                    v_isSharedCheck_4454_ = (!lean_is_exclusive(v___x_4428_)) as u8;
                    if v_isSharedCheck_4454_ == 0 {
                        v___x_4432_ = v___x_4428_;
                        v_isShared_4433_ = v_isSharedCheck_4454_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4430_);
                        lean_inc(v_a_4429_);
                        lean_dec(v___x_4428_);
                        v___x_4432_ = lean_box(0);
                        v_isShared_4433_ = v_isSharedCheck_4454_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4408_);
                    return v___x_4428_;
                }
            }
            1 => {
                v_task_4434_ = lean_ctor_get(v_a_4429_, 0);
                v_kind_4435_ = lean_ctor_get(v_a_4429_, 1);
                v_isSharedCheck_4452_ = (!lean_is_exclusive(v_a_4429_)) as u8;
                if v_isSharedCheck_4452_ == 0 {
                    v_unused_4453_ = lean_ctor_get(v_a_4429_, 2);
                    lean_dec(v_unused_4453_);
                    v___x_4437_ = v_a_4429_;
                    v_isShared_4438_ = v_isSharedCheck_4452_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_4435_);
                    lean_inc(v_task_4434_);
                    lean_dec(v_a_4429_);
                    v___x_4437_ = lean_box(0);
                    v_isShared_4438_ = v_isSharedCheck_4452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_4439_ = lean_ctor_get(v_a_4399_, 3);
                v___x_4440_ = lean_st_ref_take(v_registeredJobs_4439_);
                v___x_4441_ = lean_string_append(v___x_4408_, v___x_4409_);
                if v_isShared_4438_ == 0 {
                    lean_ctor_set(v___x_4437_, 2, v___x_4441_);
                    v_job_4443_ = v___x_4437_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_task_4434_);
                    lean_ctor_set(v_reuseFailAlloc_4451_, 1, v_kind_4435_);
                    lean_ctor_set(v_reuseFailAlloc_4451_, 2, v___x_4441_);
                    v_job_4443_ = v_reuseFailAlloc_4451_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_4443_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4418_,
                );
                lean_inc_ref(v_job_4443_);
                v___x_4444_ = l_Lake_Job_toOpaque___redArg(v_job_4443_);
                v___x_4445_ = lean_array_push(v___x_4440_, v___x_4444_);
                v___x_4446_ = lean_st_ref_set(v_registeredJobs_4439_, v___x_4445_);
                v___x_4447_ = l_Lake_Job_renew___redArg(v_job_4443_);
                if v_isShared_4433_ == 0 {
                    lean_ctor_set(v___x_4432_, 0, v___x_4447_);
                    v___x_4449_ = v___x_4432_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
                    lean_ctor_set(v_reuseFailAlloc_4450_, 1, v_a_4430_);
                    v___x_4449_ = v_reuseFailAlloc_4450_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(
    mut v_self_4455_: *mut LeanObject,
    mut v_a_4456_: *mut LeanObject,
    mut v_a_4457_: *mut LeanObject,
    mut v_a_4458_: *mut LeanObject,
    mut v_a_4459_: *mut LeanObject,
    mut v_a_4460_: *mut LeanObject,
    mut v_a_4461_: *mut LeanObject,
    mut v_a_4462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4463_: *mut LeanObject = core::ptr::null_mut();
    v_res_4463_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(
        v_self_4455_,
        v_a_4456_,
        v_a_4457_,
        v_a_4458_,
        v_a_4459_,
        v_a_4460_,
        v_a_4461_,
    );
    lean_dec_ref(v_a_4460_);
    lean_dec(v_a_4459_);
    lean_dec(v_a_4458_);
    lean_dec(v_a_4457_);
    return v_res_4463_;
}
pub unsafe fn _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    v___x_4464_ = lean_box(0);
    v___x_4465_ = l_Lean_Json_compress(v___x_4464_);
    return v___x_4465_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(
    mut v_fmt_4466_: u8,
) -> *mut LeanObject {
    if v_fmt_4466_ == 0 {
        let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
        v___x_4467_ =
            l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
        return v___x_4467_;
    } else {
        let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
        v___x_4468_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once), _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
        return v___x_4468_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(
    mut v_fmt_4469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_4470_: u8 = 0;
    let mut v_res_4471_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_4470_ = (lean_unbox(v_fmt_4469_) as u8);
    v_res_4471_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(
        v_fmt_boxed_4470_,
    );
    return v_res_4471_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(
    mut v_fmt_4472_: u8,
    mut v_a_4473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    v___x_4474_ =
        l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_4472_);
    return v___x_4474_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(
    mut v_fmt_4475_: *mut LeanObject,
    mut v_a_4476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fmt_boxed_4477_: u8 = 0;
    let mut v_res_4478_: *mut LeanObject = core::ptr::null_mut();
    v_fmt_boxed_4477_ = (lean_unbox(v_fmt_4475_) as u8);
    v_res_4478_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(
        v_fmt_boxed_4477_,
        v_a_4476_,
    );
    return v_res_4478_;
}
pub unsafe fn l_Lake_Package_extraDepFacetConfig___lam__0(
    mut v___y_4479_: u8,
    mut v___y_4480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    v___x_4481_ =
        l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_4479_);
    return v___x_4481_;
}
pub unsafe fn l_Lake_Package_extraDepFacetConfig___lam__0___boxed(
    mut v___y_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_67__boxed_4484_: u8 = 0;
    let mut v_res_4485_: *mut LeanObject = core::ptr::null_mut();
    v___y_67__boxed_4484_ = (lean_unbox(v___y_4482_) as u8);
    v_res_4485_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_4484_, v___y_4483_);
    return v_res_4485_;
}
pub unsafe fn _init_l_Lake_Package_extraDepFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___f_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    v___f_4488_ = l_Lake_Package_extraDepFacetConfig___closed__0;
    v___x_4489_ = 1;
    v___x_4490_ = l_Lake_instDataKindUnit;
    v___x_4491_ = l_Lake_Package_extraDepFacetConfig___closed__1;
    v___x_4492_ = l_Lake_Package_keyword;
    v___x_4493_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_4493_, 0, v___x_4492_);
    lean_ctor_set(v___x_4493_, 1, v___x_4491_);
    lean_ctor_set(v___x_4493_, 2, v___x_4490_);
    lean_ctor_set(v___x_4493_, 3, v___f_4488_);
    lean_ctor_set_uint8(
        v___x_4493_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_4489_,
    );
    lean_ctor_set_uint8(
        v___x_4493_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_4489_,
    );
    return v___x_4493_;
}
pub unsafe fn _init_l_Lake_Package_extraDepFacetConfig() -> *mut LeanObject {
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    v___x_4494_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_extraDepFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Package_extraDepFacetConfig___closed__2_once),
        _init_l_Lake_Package_extraDepFacetConfig___closed__2,
    );
    return v___x_4494_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(
    mut v_self_4510_: *mut LeanObject,
    mut v_a_4511_: *mut LeanObject,
    mut v_a_4512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_origName_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4525_: u8 = 0;
    let mut v_wantsRebuild_4526_: u8 = 0;
    let mut v_trace_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toolchain_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: u8 = 0;
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4546_: u8 = 0;
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4554_: u8 = 0;
    let mut v_unused_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4559_: u8 = 0;
    let mut v_wantsRebuild_4560_: u8 = 0;
    let mut v_trace_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4573_: u8 = 0;
    let mut v_log_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4575_: u8 = 0;
    let mut v_wantsRebuild_4576_: u8 = 0;
    let mut v_trace_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_origName_4514_ = lean_ctor_get(v_self_4510_, 3);
                lean_inc(v_origName_4514_);
                v_dir_4515_ = lean_ctor_get(v_self_4510_, 4);
                lean_inc_ref(v_dir_4515_);
                v_scope_4516_ = lean_ctor_get(v_self_4510_, 10);
                lean_inc_ref(v_scope_4516_);
                lean_dec_ref(v_self_4510_);
                v___x_4517_ = lean_string_utf8_byte_size(v_scope_4516_);
                v___x_4518_ = lean_unsigned_to_nat(0);
                v___x_4519_ = lean_nat_dec_eq(v___x_4517_, v___x_4518_);
                if v___x_4519_ == 0 {
                    v___x_4520_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0;
                    v___x_4521_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_4520_, v_dir_4515_);
                    if lean_obj_tag(v___x_4521_) == 1 {
                        v_toContext_4522_ = lean_ctor_get(v_a_4511_, 1);
                        v_lakeEnv_4523_ = lean_ctor_get(v_toContext_4522_, 0);
                        v_log_4524_ = lean_ctor_get(v_a_4512_, 0);
                        v_action_4525_ = lean_ctor_get_uint8(
                            v_a_4512_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_wantsRebuild_4526_ = lean_ctor_get_uint8(
                            v_a_4512_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_trace_4527_ = lean_ctor_get(v_a_4512_, 1);
                        v_buildTime_4528_ = lean_ctor_get(v_a_4512_, 2);
                        v_val_4529_ = lean_ctor_get(v___x_4521_, 0);
                        lean_inc(v_val_4529_);
                        lean_dec_ref_known(v___x_4521_, 1);
                        v_toolchain_4530_ = lean_ctor_get(v_lakeEnv_4523_, 18);
                        v___x_4531_ = lean_string_utf8_byte_size(v_toolchain_4530_);
                        v___x_4532_ = lean_nat_dec_eq(v___x_4531_, v___x_4518_);
                        if v___x_4532_ == 0 {
                            v___x_4533_ = l_Lean_Name_toString(v_origName_4514_, v___x_4519_);
                            lean_inc_ref(v_lakeEnv_4523_);
                            v___x_4534_ = l_Lake_Reservoir_pkgApiUrl(
                                v_lakeEnv_4523_,
                                v_scope_4516_,
                                v___x_4533_,
                            );
                            v___x_4535_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1;
                            v___x_4536_ = lean_string_append(v___x_4534_, v___x_4535_);
                            v___x_4537_ = lean_string_append(v___x_4536_, v_val_4529_);
                            lean_dec(v_val_4529_);
                            v___x_4538_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2;
                            v___x_4539_ = lean_string_append(v___x_4537_, v___x_4538_);
                            v___x_4540_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                            lean_inc_ref(v_toolchain_4530_);
                            v___x_4541_ = l_Lake_uriEncode(v_toolchain_4530_, v___x_4540_);
                            v___x_4542_ = lean_string_append(v___x_4539_, v___x_4541_);
                            lean_dec_ref(v___x_4541_);
                            v___x_4543_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_4543_, 0, v___x_4542_);
                            lean_ctor_set(v___x_4543_, 1, v_a_4512_);
                            return v___x_4543_;
                        } else {
                            lean_inc(v_buildTime_4528_);
                            lean_inc_ref(v_trace_4527_);
                            lean_inc_ref(v_log_4524_);
                            lean_dec(v_val_4529_);
                            lean_dec_ref(v_scope_4516_);
                            lean_dec(v_origName_4514_);
                            v_isSharedCheck_4554_ = (!lean_is_exclusive(v_a_4512_)) as u8;
                            if v_isSharedCheck_4554_ == 0 {
                                v_unused_4555_ = lean_ctor_get(v_a_4512_, 2);
                                lean_dec(v_unused_4555_);
                                v_unused_4556_ = lean_ctor_get(v_a_4512_, 1);
                                lean_dec(v_unused_4556_);
                                v_unused_4557_ = lean_ctor_get(v_a_4512_, 0);
                                lean_dec(v_unused_4557_);
                                v___x_4545_ = v_a_4512_;
                                v_isShared_4546_ = v_isSharedCheck_4554_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_a_4512_);
                                v___x_4545_ = lean_box(0);
                                v_isShared_4546_ = v_isSharedCheck_4554_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4521_);
                        lean_dec_ref(v_scope_4516_);
                        lean_dec(v_origName_4514_);
                        v_log_4558_ = lean_ctor_get(v_a_4512_, 0);
                        v_action_4559_ = lean_ctor_get_uint8(
                            v_a_4512_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_wantsRebuild_4560_ = lean_ctor_get_uint8(
                            v_a_4512_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_trace_4561_ = lean_ctor_get(v_a_4512_, 1);
                        v_buildTime_4562_ = lean_ctor_get(v_a_4512_, 2);
                        v_isSharedCheck_4573_ = (!lean_is_exclusive(v_a_4512_)) as u8;
                        if v_isSharedCheck_4573_ == 0 {
                            v___x_4564_ = v_a_4512_;
                            v_isShared_4565_ = v_isSharedCheck_4573_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_buildTime_4562_);
                            lean_inc(v_trace_4561_);
                            lean_inc(v_log_4558_);
                            lean_dec(v_a_4512_);
                            v___x_4564_ = lean_box(0);
                            v_isShared_4565_ = v_isSharedCheck_4573_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_scope_4516_);
                    lean_dec_ref(v_dir_4515_);
                    lean_dec(v_origName_4514_);
                    v_log_4574_ = lean_ctor_get(v_a_4512_, 0);
                    v_action_4575_ = lean_ctor_get_uint8(
                        v_a_4512_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_4576_ = lean_ctor_get_uint8(
                        v_a_4512_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_4577_ = lean_ctor_get(v_a_4512_, 1);
                    v_buildTime_4578_ = lean_ctor_get(v_a_4512_, 2);
                    v_isSharedCheck_4589_ = (!lean_is_exclusive(v_a_4512_)) as u8;
                    if v_isSharedCheck_4589_ == 0 {
                        v___x_4580_ = v_a_4512_;
                        v_isShared_4581_ = v_isSharedCheck_4589_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_buildTime_4578_);
                        lean_inc(v_trace_4577_);
                        lean_inc(v_log_4574_);
                        lean_dec(v_a_4512_);
                        v___x_4580_ = lean_box(0);
                        v_isShared_4581_ = v_isSharedCheck_4589_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4547_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4;
                v___x_4548_ = lean_array_get_size(v_log_4524_);
                v___x_4549_ = lean_array_push(v_log_4524_, v___x_4547_);
                if v_isShared_4546_ == 0 {
                    lean_ctor_set(v___x_4545_, 0, v___x_4549_);
                    v___x_4551_ = v___x_4545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4549_);
                    lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_trace_4527_);
                    lean_ctor_set(v_reuseFailAlloc_4553_, 2, v_buildTime_4528_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4553_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4525_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4553_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4526_,
                    );
                    v___x_4551_ = v_reuseFailAlloc_4553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4552_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4552_, 0, v___x_4548_);
                lean_ctor_set(v___x_4552_, 1, v___x_4551_);
                return v___x_4552_;
            }
            3 => {
                v___x_4566_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6;
                v___x_4567_ = lean_array_get_size(v_log_4558_);
                v___x_4568_ = lean_array_push(v_log_4558_, v___x_4566_);
                if v_isShared_4565_ == 0 {
                    lean_ctor_set(v___x_4564_, 0, v___x_4568_);
                    v___x_4570_ = v___x_4564_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4568_);
                    lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_trace_4561_);
                    lean_ctor_set(v_reuseFailAlloc_4572_, 2, v_buildTime_4562_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4572_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4559_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4572_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4560_,
                    );
                    v___x_4570_ = v_reuseFailAlloc_4572_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4571_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4571_, 0, v___x_4567_);
                lean_ctor_set(v___x_4571_, 1, v___x_4570_);
                return v___x_4571_;
            }
            5 => {
                v___x_4582_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8;
                v___x_4583_ = lean_array_get_size(v_log_4574_);
                v___x_4584_ = lean_array_push(v_log_4574_, v___x_4582_);
                if v_isShared_4581_ == 0 {
                    lean_ctor_set(v___x_4580_, 0, v___x_4584_);
                    v___x_4586_ = v___x_4580_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4584_);
                    lean_ctor_set(v_reuseFailAlloc_4588_, 1, v_trace_4577_);
                    lean_ctor_set(v_reuseFailAlloc_4588_, 2, v_buildTime_4578_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4588_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4575_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4588_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4576_,
                    );
                    v___x_4586_ = v_reuseFailAlloc_4588_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4587_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4587_, 0, v___x_4583_);
                lean_ctor_set(v___x_4587_, 1, v___x_4586_);
                return v___x_4587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(
    mut v_self_4590_: *mut LeanObject,
    mut v_a_4591_: *mut LeanObject,
    mut v_a_4592_: *mut LeanObject,
    mut v_a_4593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4594_: *mut LeanObject = core::ptr::null_mut();
    v_res_4594_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(
        v_self_4590_,
        v_a_4591_,
        v_a_4592_,
    );
    lean_dec_ref(v_a_4591_);
    return v_res_4594_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(
    mut v_self_4595_: *mut LeanObject,
    mut v_a_4596_: *mut LeanObject,
    mut v_a_4597_: *mut LeanObject,
    mut v_a_4598_: *mut LeanObject,
    mut v_a_4599_: *mut LeanObject,
    mut v_a_4600_: *mut LeanObject,
    mut v_a_4601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    v___x_4603_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(
        v_self_4595_,
        v_a_4600_,
        v_a_4601_,
    );
    return v___x_4603_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(
    mut v_self_4604_: *mut LeanObject,
    mut v_a_4605_: *mut LeanObject,
    mut v_a_4606_: *mut LeanObject,
    mut v_a_4607_: *mut LeanObject,
    mut v_a_4608_: *mut LeanObject,
    mut v_a_4609_: *mut LeanObject,
    mut v_a_4610_: *mut LeanObject,
    mut v_a_4611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4612_: *mut LeanObject = core::ptr::null_mut();
    v_res_4612_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(
        v_self_4604_,
        v_a_4605_,
        v_a_4606_,
        v_a_4607_,
        v_a_4608_,
        v_a_4609_,
        v_a_4610_,
    );
    lean_dec_ref(v_a_4609_);
    lean_dec(v_a_4608_);
    lean_dec(v_a_4607_);
    lean_dec(v_a_4606_);
    lean_dec_ref(v_a_4605_);
    return v_res_4612_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(
    mut v_self_4622_: *mut LeanObject,
    mut v_a_4623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rev_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4628_: u8 = 0;
    let mut v_wantsRebuild_4629_: u8 = 0;
    let mut v_trace_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remoteUrl_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildArchive_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4645_: u8 = 0;
    let mut v___y_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4647_: u8 = 0;
    let mut v___y_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4674_: u8 = 0;
    let mut v_wantsRebuild_4675_: u8 = 0;
    let mut v_trace_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4680_: u8 = 0;
    let mut v_wantsRebuild_4681_: u8 = 0;
    let mut v_trace_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4686_: u8 = 0;
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut v_log_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4696_: u8 = 0;
    let mut v_wantsRebuild_4697_: u8 = 0;
    let mut v_trace_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_releaseRepo_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: u8 = 0;
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_dir_4640_ = lean_ctor_get(v_self_4622_, 4);
                lean_inc_ref(v_dir_4640_);
                v_config_4641_ = lean_ctor_get(v_self_4622_, 6);
                lean_inc_ref(v_config_4641_);
                v_remoteUrl_4642_ = lean_ctor_get(v_self_4622_, 11);
                lean_inc_ref(v_remoteUrl_4642_);
                v_buildArchive_4643_ = lean_ctor_get(v_self_4622_, 20);
                lean_inc_ref(v_buildArchive_4643_);
                lean_dec_ref(v_self_4622_);
                v_releaseRepo_4701_ = lean_ctor_get(v_config_4641_, 10);
                lean_inc(v_releaseRepo_4701_);
                lean_dec_ref(v_config_4641_);
                if lean_obj_tag(v_releaseRepo_4701_) == 0 {
                    v___x_4702_ = lean_string_utf8_byte_size(v_remoteUrl_4642_);
                    v___x_4703_ = lean_unsigned_to_nat(0);
                    v___x_4704_ = lean_nat_dec_eq(v___x_4702_, v___x_4703_);
                    if v___x_4704_ == 0 {
                        lean_dec_ref(v_remoteUrl_4642_);
                        v___y_4670_ = v_releaseRepo_4701_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4705_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4705_, 0, v_remoteUrl_4642_);
                        v___y_4670_ = v___x_4705_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_remoteUrl_4642_);
                    v___y_4670_ = v_releaseRepo_4701_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_4632_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0;
                v___x_4633_ = lean_string_append(v___x_4632_, v_rev_4626_);
                lean_dec_ref(v_rev_4626_);
                v___x_4634_ = 3;
                v___x_4635_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4635_, 0, v___x_4633_);
                lean_ctor_set_uint8(
                    v___x_4635_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4634_,
                );
                v___x_4636_ = lean_array_get_size(v_log_4627_);
                v___x_4637_ = lean_array_push(v_log_4627_, v___x_4635_);
                v___x_4638_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_4638_, 0, v___x_4637_);
                lean_ctor_set(v___x_4638_, 1, v_trace_4630_);
                lean_ctor_set(v___x_4638_, 2, v_buildTime_4631_);
                lean_ctor_set_uint8(
                    v___x_4638_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_action_4628_,
                );
                lean_ctor_set_uint8(
                    v___x_4638_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v_wantsRebuild_4629_,
                );
                v___x_4639_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4639_, 0, v___x_4636_);
                lean_ctor_set(v___x_4639_, 1, v___x_4638_);
                return v___x_4639_;
            }
            2 => {
                v___x_4651_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0;
                lean_inc_ref(v_dir_4640_);
                v___x_4652_ = l_Lake_GitRepo_findTag_x3f(v___x_4651_, v_dir_4640_);
                if lean_obj_tag(v___x_4652_) == 1 {
                    lean_dec_ref(v_dir_4640_);
                    v_val_4653_ = lean_ctor_get(v___x_4652_, 0);
                    lean_inc(v_val_4653_);
                    lean_dec_ref_known(v___x_4652_, 1);
                    v___x_4654_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v___x_4654_, 0, v___y_4649_);
                    lean_ctor_set(v___x_4654_, 1, v___y_4648_);
                    lean_ctor_set(v___x_4654_, 2, v___y_4646_);
                    lean_ctor_set_uint8(
                        v___x_4654_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___y_4645_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4654_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v___y_4647_,
                    );
                    v___x_4655_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1;
                    v___x_4656_ = lean_string_append(v_val_4650_, v___x_4655_);
                    v___x_4657_ = lean_string_append(v___x_4656_, v_val_4653_);
                    lean_dec(v_val_4653_);
                    v___x_4658_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2;
                    v___x_4659_ = lean_string_append(v___x_4657_, v___x_4658_);
                    v___x_4660_ = lean_string_append(v___x_4659_, v_buildArchive_4643_);
                    lean_dec_ref(v_buildArchive_4643_);
                    v___x_4661_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4661_, 0, v___x_4660_);
                    lean_ctor_set(v___x_4661_, 1, v___x_4654_);
                    return v___x_4661_;
                } else {
                    lean_dec(v___x_4652_);
                    lean_dec_ref(v_val_4650_);
                    lean_dec_ref(v_buildArchive_4643_);
                    v___x_4662_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_4651_, v_dir_4640_);
                    if lean_obj_tag(v___x_4662_) == 1 {
                        v_val_4663_ = lean_ctor_get(v___x_4662_, 0);
                        lean_inc(v_val_4663_);
                        lean_dec_ref_known(v___x_4662_, 1);
                        v___x_4664_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3;
                        v___x_4665_ = lean_string_append(v___x_4664_, v_val_4663_);
                        lean_dec(v_val_4663_);
                        v___x_4666_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4;
                        v___x_4667_ = lean_string_append(v___x_4665_, v___x_4666_);
                        v_rev_4626_ = v___x_4667_;
                        v_log_4627_ = v___y_4649_;
                        v_action_4628_ = v___y_4645_;
                        v_wantsRebuild_4629_ = v___y_4647_;
                        v_trace_4630_ = v___y_4648_;
                        v_buildTime_4631_ = v___y_4646_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4662_);
                        v___x_4668_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                        v_rev_4626_ = v___x_4668_;
                        v_log_4627_ = v___y_4649_;
                        v_action_4628_ = v___y_4645_;
                        v_wantsRebuild_4629_ = v___y_4647_;
                        v_trace_4630_ = v___y_4648_;
                        v_buildTime_4631_ = v___y_4646_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4671_ = l_Lake_Git_defaultRemote;
                lean_inc_ref(v_dir_4640_);
                v___x_4672_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_4671_, v_dir_4640_);
                if lean_obj_tag(v___y_4670_) == 0 {
                    if lean_obj_tag(v___x_4672_) == 1 {
                        v_log_4673_ = lean_ctor_get(v_a_4623_, 0);
                        lean_inc_ref(v_log_4673_);
                        v_action_4674_ = lean_ctor_get_uint8(
                            v_a_4623_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_wantsRebuild_4675_ = lean_ctor_get_uint8(
                            v_a_4623_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_trace_4676_ = lean_ctor_get(v_a_4623_, 1);
                        lean_inc_ref(v_trace_4676_);
                        v_buildTime_4677_ = lean_ctor_get(v_a_4623_, 2);
                        lean_inc(v_buildTime_4677_);
                        lean_dec_ref(v_a_4623_);
                        v_val_4678_ = lean_ctor_get(v___x_4672_, 0);
                        lean_inc(v_val_4678_);
                        lean_dec_ref_known(v___x_4672_, 1);
                        v___y_4645_ = v_action_4674_;
                        v___y_4646_ = v_buildTime_4677_;
                        v___y_4647_ = v_wantsRebuild_4675_;
                        v___y_4648_ = v_trace_4676_;
                        v___y_4649_ = v_log_4673_;
                        v_val_4650_ = v_val_4678_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_4672_);
                        lean_dec_ref(v_buildArchive_4643_);
                        lean_dec_ref(v_dir_4640_);
                        v_log_4679_ = lean_ctor_get(v_a_4623_, 0);
                        v_action_4680_ = lean_ctor_get_uint8(
                            v_a_4623_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_wantsRebuild_4681_ = lean_ctor_get_uint8(
                            v_a_4623_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_trace_4682_ = lean_ctor_get(v_a_4623_, 1);
                        v_buildTime_4683_ = lean_ctor_get(v_a_4623_, 2);
                        v_isSharedCheck_4694_ = (!lean_is_exclusive(v_a_4623_)) as u8;
                        if v_isSharedCheck_4694_ == 0 {
                            v___x_4685_ = v_a_4623_;
                            v_isShared_4686_ = v_isSharedCheck_4694_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_buildTime_4683_);
                            lean_inc(v_trace_4682_);
                            lean_inc(v_log_4679_);
                            lean_dec(v_a_4623_);
                            v___x_4685_ = lean_box(0);
                            v_isShared_4686_ = v_isSharedCheck_4694_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4672_);
                    v_log_4695_ = lean_ctor_get(v_a_4623_, 0);
                    lean_inc_ref(v_log_4695_);
                    v_action_4696_ = lean_ctor_get_uint8(
                        v_a_4623_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_4697_ = lean_ctor_get_uint8(
                        v_a_4623_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_4698_ = lean_ctor_get(v_a_4623_, 1);
                    lean_inc_ref(v_trace_4698_);
                    v_buildTime_4699_ = lean_ctor_get(v_a_4623_, 2);
                    lean_inc(v_buildTime_4699_);
                    lean_dec_ref(v_a_4623_);
                    v_val_4700_ = lean_ctor_get(v___y_4670_, 0);
                    lean_inc(v_val_4700_);
                    lean_dec_ref_known(v___y_4670_, 1);
                    v___y_4645_ = v_action_4696_;
                    v___y_4646_ = v_buildTime_4699_;
                    v___y_4647_ = v_wantsRebuild_4697_;
                    v___y_4648_ = v_trace_4698_;
                    v___y_4649_ = v_log_4695_;
                    v_val_4650_ = v_val_4700_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_4687_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6;
                v___x_4688_ = lean_array_get_size(v_log_4679_);
                v___x_4689_ = lean_array_push(v_log_4679_, v___x_4687_);
                if v_isShared_4686_ == 0 {
                    lean_ctor_set(v___x_4685_, 0, v___x_4689_);
                    v___x_4691_ = v___x_4685_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4689_);
                    lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_trace_4682_);
                    lean_ctor_set(v_reuseFailAlloc_4693_, 2, v_buildTime_4683_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4693_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4680_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4693_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4681_,
                    );
                    v___x_4691_ = v_reuseFailAlloc_4693_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4692_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4692_, 0, v___x_4688_);
                lean_ctor_set(v___x_4692_, 1, v___x_4691_);
                return v___x_4692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(
    mut v_self_4706_: *mut LeanObject,
    mut v_a_4707_: *mut LeanObject,
    mut v_a_4708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4709_: *mut LeanObject = core::ptr::null_mut();
    v_res_4709_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(
        v_self_4706_,
        v_a_4707_,
    );
    return v_res_4709_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(
    mut v_self_4710_: *mut LeanObject,
    mut v_a_4711_: *mut LeanObject,
    mut v_a_4712_: *mut LeanObject,
    mut v_a_4713_: *mut LeanObject,
    mut v_a_4714_: *mut LeanObject,
    mut v_a_4715_: *mut LeanObject,
    mut v_a_4716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    v___x_4718_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(
        v_self_4710_,
        v_a_4716_,
    );
    return v___x_4718_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(
    mut v_self_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
    mut v_a_4722_: *mut LeanObject,
    mut v_a_4723_: *mut LeanObject,
    mut v_a_4724_: *mut LeanObject,
    mut v_a_4725_: *mut LeanObject,
    mut v_a_4726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4727_: *mut LeanObject = core::ptr::null_mut();
    v_res_4727_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(
        v_self_4719_,
        v_a_4720_,
        v_a_4721_,
        v_a_4722_,
        v_a_4723_,
        v_a_4724_,
        v_a_4725_,
    );
    lean_dec_ref(v_a_4724_);
    lean_dec(v_a_4723_);
    lean_dec(v_a_4722_);
    lean_dec(v_a_4721_);
    lean_dec_ref(v_a_4720_);
    return v_res_4727_;
}
pub unsafe fn l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(
    mut v_val_4728_: *mut LeanObject,
    mut v_a_x3f_4729_: *mut LeanObject,
    mut v___y_4730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4734_: u8 = 0;
    let mut v_wantsRebuild_4735_: u8 = 0;
    let mut v_trace_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4740_: u8 = 0;
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4732_ = lean_io_mono_ms_now();
                v_log_4733_ = lean_ctor_get(v___y_4730_, 0);
                v_action_4734_ = lean_ctor_get_uint8(
                    v___y_4730_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4735_ = lean_ctor_get_uint8(
                    v___y_4730_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4736_ = lean_ctor_get(v___y_4730_, 1);
                v_buildTime_4737_ = lean_ctor_get(v___y_4730_, 2);
                v_isSharedCheck_4748_ = (!lean_is_exclusive(v___y_4730_)) as u8;
                if v_isSharedCheck_4748_ == 0 {
                    v___x_4739_ = v___y_4730_;
                    v_isShared_4740_ = v_isSharedCheck_4748_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buildTime_4737_);
                    lean_inc(v_trace_4736_);
                    lean_inc(v_log_4733_);
                    lean_dec(v___y_4730_);
                    v___x_4739_ = lean_box(0);
                    v_isShared_4740_ = v_isSharedCheck_4748_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4741_ = lean_nat_sub(v___x_4732_, v_val_4728_);
                lean_dec(v___x_4732_);
                v___x_4742_ = lean_box(0);
                v___x_4743_ = lean_nat_add(v_buildTime_4737_, v___x_4741_);
                lean_dec(v___x_4741_);
                lean_dec(v_buildTime_4737_);
                if v_isShared_4740_ == 0 {
                    lean_ctor_set(v___x_4739_, 2, v___x_4743_);
                    v___x_4745_ = v___x_4739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_log_4733_);
                    lean_ctor_set(v_reuseFailAlloc_4747_, 1, v_trace_4736_);
                    lean_ctor_set(v_reuseFailAlloc_4747_, 2, v___x_4743_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4747_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_4734_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4747_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4735_,
                    );
                    v___x_4745_ = v_reuseFailAlloc_4747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4746_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4746_, 0, v___x_4742_);
                lean_ctor_set(v___x_4746_, 1, v___x_4745_);
                return v___x_4746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(
    mut v_val_4749_: *mut LeanObject,
    mut v_a_x3f_4750_: *mut LeanObject,
    mut v___y_4751_: *mut LeanObject,
    mut v___y_4752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4753_: *mut LeanObject = core::ptr::null_mut();
    v_res_4753_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_4749_, v_a_x3f_4750_, v___y_4751_);
    lean_dec(v_a_x3f_4750_);
    lean_dec(v_val_4749_);
    return v_res_4753_;
}
pub unsafe fn l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(
    mut v_url_4759_: *mut LeanObject,
    mut v_archiveFile_4760_: *mut LeanObject,
    mut v_headers_4761_: *mut LeanObject,
    mut v_depTrace_4762_: *mut LeanObject,
    mut v_traceFile_4763_: *mut LeanObject,
    mut v_action_4764_: u8,
    mut v_a_4765_: *mut LeanObject,
    mut v_a_4766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4774_: u8 = 0;
    let mut v_wantsRebuild_4775_: u8 = 0;
    let mut v_trace_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBuildConfig_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_4785_: u8 = 0;
    let mut v_wantsRebuild_4786_: u8 = 0;
    let mut v_trace_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4791_: u8 = 0;
    let mut v_noBuild_4792_: u8 = 0;
    let mut v___x_4793_: u8 = 0;
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4814_: u8 = 0;
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4818_: u8 = 0;
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4829_: u8 = 0;
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4833_: u8 = 0;
    let mut v_unused_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_unused_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: u8 = 0;
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut v_unused_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: u8 = 0;
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBuildConfig_4783_ = lean_ctor_get(v_a_4765_, 0);
                v_log_4784_ = lean_ctor_get(v_a_4766_, 0);
                v_action_4785_ = lean_ctor_get_uint8(
                    v_a_4766_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4786_ = lean_ctor_get_uint8(
                    v_a_4766_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4787_ = lean_ctor_get(v_a_4766_, 1);
                v_buildTime_4788_ = lean_ctor_get(v_a_4766_, 2);
                v_isSharedCheck_4878_ = (!lean_is_exclusive(v_a_4766_)) as u8;
                if v_isSharedCheck_4878_ == 0 {
                    v___x_4790_ = v_a_4766_;
                    v_isShared_4791_ = v_isSharedCheck_4878_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_buildTime_4788_);
                    lean_inc(v_trace_4787_);
                    lean_inc(v_log_4784_);
                    lean_dec(v_a_4766_);
                    v___x_4790_ = lean_box(0);
                    v_isShared_4791_ = v_isSharedCheck_4878_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_4771_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4771_, 0, v_a_4769_);
                lean_ctor_set(v___x_4771_, 1, v_a_4770_);
                return v___x_4771_;
            }
            2 => {
                v___x_4778_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1;
                v___x_4779_ = lean_array_get_size(v_log_4773_);
                v___x_4780_ = lean_array_push(v_log_4773_, v___x_4778_);
                v___x_4781_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_4781_, 0, v___x_4780_);
                lean_ctor_set(v___x_4781_, 1, v_trace_4776_);
                lean_ctor_set(v___x_4781_, 2, v_buildTime_4777_);
                lean_ctor_set_uint8(
                    v___x_4781_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_action_4774_,
                );
                lean_ctor_set_uint8(
                    v___x_4781_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v_wantsRebuild_4775_,
                );
                v___x_4782_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4782_, 0, v___x_4779_);
                lean_ctor_set(v___x_4782_, 1, v___x_4781_);
                return v___x_4782_;
            }
            3 => {
                v_noBuild_4792_ = lean_ctor_get_uint8(
                    v_toBuildConfig_4783_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v___x_4793_ = l_Lake_JobAction_merge(v_action_4785_, v_action_4764_);
                v___x_4794_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2;
                lean_inc_ref(v_traceFile_4763_);
                v___x_4795_ = l_System_FilePath_addExtension(v_traceFile_4763_, v___x_4794_);
                if v_noBuild_4792_ == 0 {
                    v___x_4796_ = lean_io_mono_ms_now();
                    lean_inc_ref(v_log_4784_);
                    v___x_4797_ = l_Lake_download(
                        v_url_4759_,
                        v_archiveFile_4760_,
                        v_headers_4761_,
                        v_log_4784_,
                    );
                    if lean_obj_tag(v___x_4797_) == 0 {
                        v_a_4804_ = lean_ctor_get(v___x_4797_, 0);
                        lean_inc(v_a_4804_);
                        v_a_4805_ = lean_ctor_get(v___x_4797_, 1);
                        lean_inc(v_a_4805_);
                        lean_dec_ref_known(v___x_4797_, 2);
                        v___x_4806_ = lean_array_get_size(v_log_4784_);
                        lean_dec_ref(v_log_4784_);
                        v___x_4807_ = lean_array_get_size(v_a_4805_);
                        v___x_4808_ = l_Array_extract___redArg(v_a_4805_, v___x_4806_, v___x_4807_);
                        v___x_4809_ = lean_box(0);
                        v___x_4810_ =
                            l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(
                                v_depTrace_4762_,
                                v___x_4809_,
                                v___x_4808_,
                            );
                        v___x_4811_ =
                            l_Lake_BuildMetadata_writeFile(v_traceFile_4763_, v___x_4810_);
                        if lean_obj_tag(v___x_4811_) == 0 {
                            v_isSharedCheck_4848_ = (!lean_is_exclusive(v___x_4811_)) as u8;
                            if v_isSharedCheck_4848_ == 0 {
                                v_unused_4849_ = lean_ctor_get(v___x_4811_, 0);
                                lean_dec(v_unused_4849_);
                                v___x_4813_ = v___x_4811_;
                                v_isShared_4814_ = v_isSharedCheck_4848_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_4811_);
                                v___x_4813_ = lean_box(0);
                                v_isShared_4814_ = v_isSharedCheck_4848_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4804_);
                            lean_dec_ref(v___x_4795_);
                            v_a_4850_ = lean_ctor_get(v___x_4811_, 0);
                            lean_inc(v_a_4850_);
                            lean_dec_ref_known(v___x_4811_, 1);
                            v___x_4851_ = lean_io_error_to_string(v_a_4850_);
                            v___x_4852_ = 3;
                            v___x_4853_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_4853_, 0, v___x_4851_);
                            lean_ctor_set_uint8(
                                v___x_4853_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_4852_,
                            );
                            v___x_4854_ = lean_array_push(v_a_4805_, v___x_4853_);
                            if v_isShared_4791_ == 0 {
                                lean_ctor_set(v___x_4790_, 0, v___x_4854_);
                                v___x_4856_ = v___x_4790_;
                                state = 13;
                                continue;
                            } else {
                                v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 3, (2) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4854_);
                                lean_ctor_set(v_reuseFailAlloc_4857_, 1, v_trace_4787_);
                                lean_ctor_set(v_reuseFailAlloc_4857_, 2, v_buildTime_4788_);
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_4857_,
                                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                                    v_wantsRebuild_4786_,
                                );
                                v___x_4856_ = v_reuseFailAlloc_4857_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_4795_);
                        lean_dec_ref(v_log_4784_);
                        lean_dec_ref(v_traceFile_4763_);
                        v_a_4858_ = lean_ctor_get(v___x_4797_, 0);
                        lean_inc(v_a_4858_);
                        v_a_4859_ = lean_ctor_get(v___x_4797_, 1);
                        lean_inc(v_a_4859_);
                        lean_dec_ref_known(v___x_4797_, 2);
                        if v_isShared_4791_ == 0 {
                            lean_ctor_set(v___x_4790_, 0, v_a_4859_);
                            v___x_4861_ = v___x_4790_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 3, (2) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4859_);
                            lean_ctor_set(v_reuseFailAlloc_4862_, 1, v_trace_4787_);
                            lean_ctor_set(v_reuseFailAlloc_4862_, 2, v_buildTime_4788_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_4862_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                                v_wantsRebuild_4786_,
                            );
                            v___x_4861_ = v_reuseFailAlloc_4862_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_archiveFile_4760_);
                    lean_dec_ref(v_url_4759_);
                    v___x_4863_ = l_System_FilePath_pathExists(v_traceFile_4763_);
                    lean_dec_ref(v_traceFile_4763_);
                    if v___x_4863_ == 0 {
                        lean_dec_ref(v___x_4795_);
                        lean_del_object(v___x_4790_);
                        v_log_4773_ = v_log_4784_;
                        v_action_4774_ = v___x_4793_;
                        v_wantsRebuild_4775_ = v_noBuild_4792_;
                        v_trace_4776_ = v_trace_4787_;
                        v_buildTime_4777_ = v_buildTime_4788_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4864_ = lean_box(0);
                        v___x_4865_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0;
                        v___x_4866_ =
                            l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(
                                v_depTrace_4762_,
                                v___x_4864_,
                                v___x_4865_,
                            );
                        v___x_4867_ = l_Lake_BuildMetadata_writeFile(v___x_4795_, v___x_4866_);
                        if lean_obj_tag(v___x_4867_) == 0 {
                            lean_dec_ref_known(v___x_4867_, 1);
                            lean_del_object(v___x_4790_);
                            v_log_4773_ = v_log_4784_;
                            v_action_4774_ = v___x_4793_;
                            v_wantsRebuild_4775_ = v_noBuild_4792_;
                            v_trace_4776_ = v_trace_4787_;
                            v_buildTime_4777_ = v_buildTime_4788_;
                            state = 2;
                            continue;
                        } else {
                            v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
                            lean_inc(v_a_4868_);
                            lean_dec_ref_known(v___x_4867_, 1);
                            v___x_4869_ = lean_io_error_to_string(v_a_4868_);
                            v___x_4870_ = 3;
                            v___x_4871_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_4871_, 0, v___x_4869_);
                            lean_ctor_set_uint8(
                                v___x_4871_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_4870_,
                            );
                            v___x_4872_ = lean_array_get_size(v_log_4784_);
                            v___x_4873_ = lean_array_push(v_log_4784_, v___x_4871_);
                            if v_isShared_4791_ == 0 {
                                lean_ctor_set(v___x_4790_, 0, v___x_4873_);
                                v___x_4875_ = v___x_4790_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 3, (2) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4873_);
                                lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_trace_4787_);
                                lean_ctor_set(v_reuseFailAlloc_4877_, 2, v_buildTime_4788_);
                                v___x_4875_ = v_reuseFailAlloc_4877_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_4801_ = lean_box(0);
                v___x_4802_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_4796_, v___x_4801_, v_a_4800_);
                lean_dec(v___x_4796_);
                v_a_4803_ = lean_ctor_get(v___x_4802_, 1);
                lean_inc(v_a_4803_);
                lean_dec_ref(v___x_4802_);
                v_a_4769_ = v_a_4799_;
                v_a_4770_ = v_a_4803_;
                state = 1;
                continue;
            }
            5 => {
                v___x_4815_ = l_Lake_removeFileIfExists(v___x_4795_);
                lean_dec_ref(v___x_4795_);
                if lean_obj_tag(v___x_4815_) == 0 {
                    v_isSharedCheck_4838_ = (!lean_is_exclusive(v___x_4815_)) as u8;
                    if v_isSharedCheck_4838_ == 0 {
                        v_unused_4839_ = lean_ctor_get(v___x_4815_, 0);
                        lean_dec(v_unused_4839_);
                        v___x_4817_ = v___x_4815_;
                        v_isShared_4818_ = v_isSharedCheck_4838_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v___x_4815_);
                        v___x_4817_ = lean_box(0);
                        v_isShared_4818_ = v_isSharedCheck_4838_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4813_);
                    lean_dec(v_a_4804_);
                    v_a_4840_ = lean_ctor_get(v___x_4815_, 0);
                    lean_inc(v_a_4840_);
                    lean_dec_ref_known(v___x_4815_, 1);
                    v___x_4841_ = lean_io_error_to_string(v_a_4840_);
                    v___x_4842_ = 3;
                    v___x_4843_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_4843_, 0, v___x_4841_);
                    lean_ctor_set_uint8(
                        v___x_4843_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_4842_,
                    );
                    v___x_4844_ = lean_array_push(v_a_4805_, v___x_4843_);
                    if v_isShared_4791_ == 0 {
                        lean_ctor_set(v___x_4790_, 0, v___x_4844_);
                        v___x_4846_ = v___x_4790_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 3, (2) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4844_);
                        lean_ctor_set(v_reuseFailAlloc_4847_, 1, v_trace_4787_);
                        lean_ctor_set(v_reuseFailAlloc_4847_, 2, v_buildTime_4788_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_4847_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_wantsRebuild_4786_,
                        );
                        v___x_4846_ = v_reuseFailAlloc_4847_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4791_ == 0 {
                    lean_ctor_set(v___x_4790_, 0, v_a_4805_);
                    v___x_4820_ = v___x_4790_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4805_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 1, v_trace_4787_);
                    lean_ctor_set(v_reuseFailAlloc_4837_, 2, v_buildTime_4788_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4837_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4786_,
                    );
                    v___x_4820_ = v_reuseFailAlloc_4837_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_4820_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4793_,
                );
                lean_inc(v_a_4804_);
                if v_isShared_4818_ == 0 {
                    lean_ctor_set(v___x_4817_, 0, v_a_4804_);
                    v___x_4822_ = v___x_4817_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4804_);
                    v___x_4822_ = v_reuseFailAlloc_4836_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4814_ == 0 {
                    lean_ctor_set_tag(v___x_4813_, 1);
                    lean_ctor_set(v___x_4813_, 0, v___x_4822_);
                    v___x_4824_ = v___x_4813_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4822_);
                    v___x_4824_ = v_reuseFailAlloc_4835_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4825_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_4796_, v___x_4824_, v___x_4820_);
                lean_dec_ref(v___x_4824_);
                lean_dec(v___x_4796_);
                v_a_4826_ = lean_ctor_get(v___x_4825_, 1);
                v_isSharedCheck_4833_ = (!lean_is_exclusive(v___x_4825_)) as u8;
                if v_isSharedCheck_4833_ == 0 {
                    v_unused_4834_ = lean_ctor_get(v___x_4825_, 0);
                    lean_dec(v_unused_4834_);
                    v___x_4828_ = v___x_4825_;
                    v_isShared_4829_ = v_isSharedCheck_4833_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_a_4826_);
                    lean_dec(v___x_4825_);
                    v___x_4828_ = lean_box(0);
                    v_isShared_4829_ = v_isSharedCheck_4833_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4829_ == 0 {
                    lean_ctor_set(v___x_4828_, 0, v_a_4804_);
                    v___x_4831_ = v___x_4828_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4804_);
                    lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_a_4826_);
                    v___x_4831_ = v_reuseFailAlloc_4832_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4831_;
            }
            12 => {
                lean_ctor_set_uint8(
                    v___x_4846_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4793_,
                );
                v_a_4799_ = v___x_4807_;
                v_a_4800_ = v___x_4846_;
                state = 4;
                continue;
            }
            13 => {
                lean_ctor_set_uint8(
                    v___x_4856_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4793_,
                );
                v_a_4799_ = v___x_4807_;
                v_a_4800_ = v___x_4856_;
                state = 4;
                continue;
            }
            14 => {
                lean_ctor_set_uint8(
                    v___x_4861_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4793_,
                );
                v_a_4799_ = v_a_4858_;
                v_a_4800_ = v___x_4861_;
                state = 4;
                continue;
            }
            15 => {
                lean_ctor_set_uint8(
                    v___x_4875_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4793_,
                );
                lean_ctor_set_uint8(
                    v___x_4875_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v_noBuild_4792_,
                );
                v___x_4876_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4876_, 0, v___x_4872_);
                lean_ctor_set(v___x_4876_, 1, v___x_4875_);
                return v___x_4876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(
    mut v_url_4879_: *mut LeanObject,
    mut v_archiveFile_4880_: *mut LeanObject,
    mut v_headers_4881_: *mut LeanObject,
    mut v_depTrace_4882_: *mut LeanObject,
    mut v_traceFile_4883_: *mut LeanObject,
    mut v_action_4884_: *mut LeanObject,
    mut v_a_4885_: *mut LeanObject,
    mut v_a_4886_: *mut LeanObject,
    mut v_a_4887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_action_boxed_4888_: u8 = 0;
    let mut v_res_4889_: *mut LeanObject = core::ptr::null_mut();
    v_action_boxed_4888_ = (lean_unbox(v_action_4884_) as u8);
    v_res_4889_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_4879_, v_archiveFile_4880_, v_headers_4881_, v_depTrace_4882_, v_traceFile_4883_, v_action_boxed_4888_, v_a_4885_, v_a_4886_);
    lean_dec_ref(v_a_4885_);
    lean_dec_ref(v_depTrace_4882_);
    lean_dec_ref(v_headers_4881_);
    return v_res_4889_;
}
pub unsafe fn l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(
    mut v_url_4890_: *mut LeanObject,
    mut v_archiveFile_4891_: *mut LeanObject,
    mut v_headers_4892_: *mut LeanObject,
    mut v_a_4893_: *mut LeanObject,
    mut v_depTrace_4894_: *mut LeanObject,
    mut v_traceFile_4895_: *mut LeanObject,
    mut v_action_4896_: u8,
    mut v_a_4897_: *mut LeanObject,
    mut v_a_4898_: *mut LeanObject,
    mut v_a_4899_: *mut LeanObject,
    mut v_a_4900_: *mut LeanObject,
    mut v_a_4901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    v___x_4903_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_4890_, v_archiveFile_4891_, v_headers_4892_, v_depTrace_4894_, v_traceFile_4895_, v_action_4896_, v_a_4900_, v_a_4901_);
    return v___x_4903_;
}
pub unsafe fn l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(
    mut v_url_4904_: *mut LeanObject,
    mut v_archiveFile_4905_: *mut LeanObject,
    mut v_headers_4906_: *mut LeanObject,
    mut v_a_4907_: *mut LeanObject,
    mut v_depTrace_4908_: *mut LeanObject,
    mut v_traceFile_4909_: *mut LeanObject,
    mut v_action_4910_: *mut LeanObject,
    mut v_a_4911_: *mut LeanObject,
    mut v_a_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
    mut v_a_4916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_action_boxed_4917_: u8 = 0;
    let mut v_res_4918_: *mut LeanObject = core::ptr::null_mut();
    v_action_boxed_4917_ = (lean_unbox(v_action_4910_) as u8);
    v_res_4918_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_4904_, v_archiveFile_4905_, v_headers_4906_, v_a_4907_, v_depTrace_4908_, v_traceFile_4909_, v_action_boxed_4917_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
    lean_dec_ref(v_a_4914_);
    lean_dec(v_a_4913_);
    lean_dec(v_a_4912_);
    lean_dec(v_a_4911_);
    lean_dec_ref(v_depTrace_4908_);
    lean_dec_ref(v_a_4907_);
    lean_dec_ref(v_headers_4906_);
    return v_res_4918_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(
    mut v_x_4919_: *mut LeanObject,
    mut v_x_4920_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4919_) == 0 {
        if lean_obj_tag(v_x_4920_) == 0 {
            let mut v___x_4921_: u8 = 0;
            v___x_4921_ = 1;
            return v___x_4921_;
        } else {
            let mut v___x_4922_: u8 = 0;
            v___x_4922_ = 0;
            return v___x_4922_;
        }
    } else {
        if lean_obj_tag(v_x_4920_) == 0 {
            let mut v___x_4923_: u8 = 0;
            v___x_4923_ = 0;
            return v___x_4923_;
        } else {
            let mut v_val_4924_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_4925_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4926_: u64 = 0;
            let mut v___x_4927_: u64 = 0;
            let mut v___x_4928_: u8 = 0;
            v_val_4924_ = lean_ctor_get(v_x_4919_, 0);
            v_val_4925_ = lean_ctor_get(v_x_4920_, 0);
            v___x_4926_ = lean_unbox_uint64(v_val_4924_);
            v___x_4927_ = lean_unbox_uint64(v_val_4925_);
            v___x_4928_ = lean_uint64_dec_eq(v___x_4926_, v___x_4927_);
            return v___x_4928_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(
    mut v_x_4929_: *mut LeanObject,
    mut v_x_4930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4931_: u8 = 0;
    let mut v_r_4932_: *mut LeanObject = core::ptr::null_mut();
    v_res_4931_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_4929_, v_x_4930_);
    lean_dec(v_x_4930_);
    lean_dec(v_x_4929_);
    v_r_4932_ = lean_box((v_res_4931_) as usize);
    return v_r_4932_;
}
pub unsafe fn l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(
    mut v_info_4933_: *mut LeanObject,
    mut v_self_4934_: *mut LeanObject,
) -> u8 {
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    v___x_4936_ = lean_io_metadata(v_info_4933_);
    if lean_obj_tag(v___x_4936_) == 0 {
        let mut v_a_4937_: *mut LeanObject = core::ptr::null_mut();
        let mut v_modified_4938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4939_: u8 = 0;
        v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
        lean_inc(v_a_4937_);
        lean_dec_ref_known(v___x_4936_, 1);
        v_modified_4938_ = lean_ctor_get(v_a_4937_, 1);
        lean_inc_ref(v_modified_4938_);
        lean_dec(v_a_4937_);
        v___x_4939_ = l_IO_FS_instOrdSystemTime_ord(v_self_4934_, v_modified_4938_);
        lean_dec_ref(v_modified_4938_);
        if v___x_4939_ == 0 {
            let mut v___x_4940_: u8 = 0;
            v___x_4940_ = 1;
            return v___x_4940_;
        } else {
            let mut v___x_4941_: u8 = 0;
            v___x_4941_ = 0;
            return v___x_4941_;
        }
    } else {
        let mut v___x_4942_: u8 = 0;
        lean_dec_ref_known(v___x_4936_, 1);
        v___x_4942_ = 0;
        return v___x_4942_;
    }
}
pub unsafe fn l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(
    mut v_info_4943_: *mut LeanObject,
    mut v_self_4944_: *mut LeanObject,
    mut v_a_4945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4946_: u8 = 0;
    let mut v_r_4947_: *mut LeanObject = core::ptr::null_mut();
    v_res_4946_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_4943_, v_self_4944_);
    lean_dec_ref(v_self_4944_);
    lean_dec_ref(v_info_4943_);
    v_r_4947_ = lean_box((v_res_4946_) as usize);
    return v_r_4947_;
}
pub unsafe fn l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(
    mut v_info_4948_: *mut LeanObject,
    mut v_depTrace_4949_: *mut LeanObject,
    mut v_depHash_4950_: *mut LeanObject,
    mut v_oldTrace_4951_: *mut LeanObject,
    mut v_a_4952_: *mut LeanObject,
    mut v_a_4953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hash_4955_: u64 = 0;
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: u8 = 0;
    v_hash_4955_ = lean_ctor_get_uint64(
        v_depTrace_4949_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v___x_4956_ = lean_box_uint64(v_hash_4955_);
    v___x_4957_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4957_, 0, v___x_4956_);
    v___x_4958_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_4957_, v_depHash_4950_);
    lean_dec_ref_known(v___x_4957_, 1);
    if v___x_4958_ == 0 {
        let mut v_toBuildConfig_4959_: *mut LeanObject = core::ptr::null_mut();
        let mut v_oldMode_4960_: u8 = 0;
        v_toBuildConfig_4959_ = lean_ctor_get(v_a_4952_, 0);
        v_oldMode_4960_ = lean_ctor_get_uint8(
            v_toBuildConfig_4959_,
            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        );
        if v_oldMode_4960_ == 0 {
            let mut v___x_4961_: u8 = 0;
            let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
            v___x_4961_ = 0;
            v___x_4962_ = lean_box((v___x_4961_) as usize);
            v___x_4963_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_4963_, 0, v___x_4962_);
            lean_ctor_set(v___x_4963_, 1, v_a_4953_);
            return v___x_4963_;
        } else {
            let mut v___x_4964_: u8 = 0;
            v___x_4964_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_4948_, v_oldTrace_4951_);
            if v___x_4964_ == 0 {
                let mut v___x_4965_: u8 = 0;
                let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
                v___x_4965_ = 0;
                v___x_4966_ = lean_box((v___x_4965_) as usize);
                v___x_4967_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4967_, 0, v___x_4966_);
                lean_ctor_set(v___x_4967_, 1, v_a_4953_);
                return v___x_4967_;
            } else {
                let mut v___x_4968_: u8 = 0;
                let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
                v___x_4968_ = 1;
                v___x_4969_ = lean_box((v___x_4968_) as usize);
                v___x_4970_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4970_, 0, v___x_4969_);
                lean_ctor_set(v___x_4970_, 1, v_a_4953_);
                return v___x_4970_;
            }
        }
    } else {
        let mut v___x_4971_: u8 = 0;
        v___x_4971_ = l_System_FilePath_pathExists(v_info_4948_);
        if v___x_4971_ == 0 {
            let mut v___x_4972_: u8 = 0;
            let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
            v___x_4972_ = 0;
            v___x_4973_ = lean_box((v___x_4972_) as usize);
            v___x_4974_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_4974_, 0, v___x_4973_);
            lean_ctor_set(v___x_4974_, 1, v_a_4953_);
            return v___x_4974_;
        } else {
            let mut v___x_4975_: u8 = 0;
            let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
            v___x_4975_ = 2;
            v___x_4976_ = lean_box((v___x_4975_) as usize);
            v___x_4977_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_4977_, 0, v___x_4976_);
            lean_ctor_set(v___x_4977_, 1, v_a_4953_);
            return v___x_4977_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(
    mut v_info_4978_: *mut LeanObject,
    mut v_depTrace_4979_: *mut LeanObject,
    mut v_depHash_4980_: *mut LeanObject,
    mut v_oldTrace_4981_: *mut LeanObject,
    mut v_a_4982_: *mut LeanObject,
    mut v_a_4983_: *mut LeanObject,
    mut v_a_4984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4985_: *mut LeanObject = core::ptr::null_mut();
    v_res_4985_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_4978_, v_depTrace_4979_, v_depHash_4980_, v_oldTrace_4981_, v_a_4982_, v_a_4983_);
    lean_dec_ref(v_a_4982_);
    lean_dec_ref(v_oldTrace_4981_);
    lean_dec(v_depHash_4980_);
    lean_dec_ref(v_depTrace_4979_);
    lean_dec_ref(v_info_4978_);
    return v_res_4985_;
}
pub unsafe fn l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(
    mut v_a_4986_: *mut LeanObject,
    mut v_info_4987_: *mut LeanObject,
    mut v_depTrace_4988_: *mut LeanObject,
    mut v_savedTrace_4989_: *mut LeanObject,
    mut v_oldTrace_4990_: *mut LeanObject,
    mut v_a_4991_: *mut LeanObject,
    mut v_a_4992_: *mut LeanObject,
    mut v_a_4993_: *mut LeanObject,
    mut v_a_4994_: *mut LeanObject,
    mut v_a_4995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5000_: u8 = 0;
    let mut v_depHash_5001_: u64 = 0;
    let mut v_log_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___y_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: u8 = 0;
    let mut v___x_5019_: u8 = 0;
    let mut v_log_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5021_: u8 = 0;
    let mut v_wantsRebuild_5022_: u8 = 0;
    let mut v_trace_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5027_: u8 = 0;
    let mut v___x_5028_: u8 = 0;
    let mut v___x_5029_: u8 = 0;
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5042_: u8 = 0;
    let mut v_reuseFailAlloc_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut v_isSharedCheck_5045_: u8 = 0;
    let mut v_reuseFailAlloc_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5047_: u8 = 0;
    let mut v_toBuildConfig_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oldMode_5049_: u8 = 0;
    let mut v___x_5050_: u8 = 0;
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: u8 = 0;
    let mut v___x_5054_: u8 = 0;
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: u8 = 0;
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_savedTrace_4989_) == 2 {
                    v_data_4997_ = lean_ctor_get(v_savedTrace_4989_, 0);
                    v_isSharedCheck_5047_ = (!lean_is_exclusive(v_savedTrace_4989_)) as u8;
                    if v_isSharedCheck_5047_ == 0 {
                        v___x_4999_ = v_savedTrace_4989_;
                        v_isShared_5000_ = v_isSharedCheck_5047_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_data_4997_);
                        lean_dec(v_savedTrace_4989_);
                        v___x_4999_ = lean_box(0);
                        v_isShared_5000_ = v_isSharedCheck_5047_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_savedTrace_4989_);
                    v_toBuildConfig_5048_ = lean_ctor_get(v_a_4994_, 0);
                    v_oldMode_5049_ = lean_ctor_get_uint8(
                        v_toBuildConfig_5048_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    if v_oldMode_5049_ == 0 {
                        v___x_5050_ = 0;
                        v___x_5051_ = lean_box((v___x_5050_) as usize);
                        v___x_5052_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5052_, 0, v___x_5051_);
                        lean_ctor_set(v___x_5052_, 1, v_a_4995_);
                        return v___x_5052_;
                    } else {
                        v___x_5053_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_4987_, v_oldTrace_4990_);
                        if v___x_5053_ == 0 {
                            v___x_5054_ = 0;
                            v___x_5055_ = lean_box((v___x_5054_) as usize);
                            v___x_5056_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_5056_, 0, v___x_5055_);
                            lean_ctor_set(v___x_5056_, 1, v_a_4995_);
                            return v___x_5056_;
                        } else {
                            v___x_5057_ = 1;
                            v___x_5058_ = lean_box((v___x_5057_) as usize);
                            v___x_5059_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_5059_, 0, v___x_5058_);
                            lean_ctor_set(v___x_5059_, 1, v_a_4995_);
                            return v___x_5059_;
                        }
                    }
                }
            }
            1 => {
                v_depHash_5001_ = lean_ctor_get_uint64(
                    v_data_4997_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_log_5002_ = lean_ctor_get(v_data_4997_, 2);
                lean_inc_ref(v_log_5002_);
                lean_dec_ref(v_data_4997_);
                v___x_5003_ = lean_box_uint64(v_depHash_5001_);
                if v_isShared_5000_ == 0 {
                    lean_ctor_set_tag(v___x_4999_, 1);
                    lean_ctor_set(v___x_4999_, 0, v___x_5003_);
                    v___x_5005_ = v___x_4999_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5003_);
                    v___x_5005_ = v_reuseFailAlloc_5046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5006_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_4987_, v_depTrace_4988_, v___x_5005_, v_oldTrace_4990_, v_a_4994_, v_a_4995_);
                lean_dec_ref(v___x_5005_);
                v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
                v_a_5008_ = lean_ctor_get(v___x_5006_, 1);
                v_isSharedCheck_5045_ = (!lean_is_exclusive(v___x_5006_)) as u8;
                if v_isSharedCheck_5045_ == 0 {
                    v___x_5010_ = v___x_5006_;
                    v_isShared_5011_ = v_isSharedCheck_5045_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_5008_);
                    lean_inc(v_a_5007_);
                    lean_dec(v___x_5006_);
                    v___x_5010_ = lean_box(0);
                    v_isShared_5011_ = v_isSharedCheck_5045_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5017_ = 0;
                v___x_5018_ = (lean_unbox(v_a_5007_) as u8);
                v___x_5019_ = l_Lake_instDecidableEqOutputStatus(v___x_5018_, v___x_5017_);
                if v___x_5019_ == 0 {
                    v_log_5020_ = lean_ctor_get(v_a_5008_, 0);
                    v_action_5021_ = lean_ctor_get_uint8(
                        v_a_5008_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_5022_ = lean_ctor_get_uint8(
                        v_a_5008_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_5023_ = lean_ctor_get(v_a_5008_, 1);
                    v_buildTime_5024_ = lean_ctor_get(v_a_5008_, 2);
                    v_isSharedCheck_5044_ = (!lean_is_exclusive(v_a_5008_)) as u8;
                    if v_isSharedCheck_5044_ == 0 {
                        v___x_5026_ = v_a_5008_;
                        v_isShared_5027_ = v_isSharedCheck_5044_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_buildTime_5024_);
                        lean_inc(v_trace_5023_);
                        lean_inc(v_log_5020_);
                        lean_dec(v_a_5008_);
                        v___x_5026_ = lean_box(0);
                        v_isShared_5027_ = v_isSharedCheck_5044_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_log_5002_);
                    v___y_5013_ = v_a_5008_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5011_ == 0 {
                    lean_ctor_set(v___x_5010_, 1, v___y_5013_);
                    v___x_5015_ = v___x_5010_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5007_);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 1, v___y_5013_);
                    v___x_5015_ = v_reuseFailAlloc_5016_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5015_;
            }
            6 => {
                v___x_5028_ = 2;
                v___x_5029_ = l_Lake_JobAction_merge(v_action_5021_, v___x_5028_);
                if v_isShared_5027_ == 0 {
                    v___x_5031_ = v___x_5026_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_log_5020_);
                    lean_ctor_set(v_reuseFailAlloc_5043_, 1, v_trace_5023_);
                    lean_ctor_set(v_reuseFailAlloc_5043_, 2, v_buildTime_5024_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5043_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5022_,
                    );
                    v___x_5031_ = v_reuseFailAlloc_5043_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_5031_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5029_,
                );
                v___x_5032_ =
                    l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(
                        v_log_5002_,
                        v_a_4986_,
                        v_a_4991_,
                        v_a_4992_,
                        v_a_4993_,
                        v_a_4994_,
                        v___x_5031_,
                    );
                lean_dec_ref(v_log_5002_);
                if lean_obj_tag(v___x_5032_) == 0 {
                    v_a_5033_ = lean_ctor_get(v___x_5032_, 1);
                    lean_inc(v_a_5033_);
                    lean_dec_ref_known(v___x_5032_, 2);
                    v___y_5013_ = v_a_5033_;
                    state = 4;
                    continue;
                } else {
                    lean_del_object(v___x_5010_);
                    lean_dec(v_a_5007_);
                    v_a_5034_ = lean_ctor_get(v___x_5032_, 0);
                    v_a_5035_ = lean_ctor_get(v___x_5032_, 1);
                    v_isSharedCheck_5042_ = (!lean_is_exclusive(v___x_5032_)) as u8;
                    if v_isSharedCheck_5042_ == 0 {
                        v___x_5037_ = v___x_5032_;
                        v_isShared_5038_ = v_isSharedCheck_5042_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5035_);
                        lean_inc(v_a_5034_);
                        lean_dec(v___x_5032_);
                        v___x_5037_ = lean_box(0);
                        v_isShared_5038_ = v_isSharedCheck_5042_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5038_ == 0 {
                    v___x_5040_ = v___x_5037_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5034_);
                    lean_ctor_set(v_reuseFailAlloc_5041_, 1, v_a_5035_);
                    v___x_5040_ = v_reuseFailAlloc_5041_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(
    mut v_a_5060_: *mut LeanObject,
    mut v_info_5061_: *mut LeanObject,
    mut v_depTrace_5062_: *mut LeanObject,
    mut v_savedTrace_5063_: *mut LeanObject,
    mut v_oldTrace_5064_: *mut LeanObject,
    mut v_a_5065_: *mut LeanObject,
    mut v_a_5066_: *mut LeanObject,
    mut v_a_5067_: *mut LeanObject,
    mut v_a_5068_: *mut LeanObject,
    mut v_a_5069_: *mut LeanObject,
    mut v_a_5070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5071_: *mut LeanObject = core::ptr::null_mut();
    v_res_5071_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_5060_, v_info_5061_, v_depTrace_5062_, v_savedTrace_5063_, v_oldTrace_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_);
    lean_dec_ref(v_a_5068_);
    lean_dec(v_a_5067_);
    lean_dec(v_a_5066_);
    lean_dec(v_a_5065_);
    lean_dec_ref(v_oldTrace_5064_);
    lean_dec_ref(v_depTrace_5062_);
    lean_dec_ref(v_info_5061_);
    lean_dec_ref(v_a_5060_);
    return v_res_5071_;
}
pub unsafe fn _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3()
-> *mut LeanObject {
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    v___x_5076_ = lean_unsigned_to_nat(0);
    v___x_5077_ = lean_nat_to_int(v___x_5076_);
    return v___x_5077_;
}
pub unsafe fn _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4()
-> *mut LeanObject {
    let mut v___x_5078_: u32 = 0;
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    v___x_5078_ = 0;
    v___x_5079_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once
        ),
        _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3,
    );
    v___x_5080_ = lean_alloc_ctor(0, 1, (4) as u32);
    lean_ctor_set(v___x_5080_, 0, v___x_5079_);
    lean_ctor_set_uint32(
        v___x_5080_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5078_,
    );
    return v___x_5080_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(
    mut v_self_5081_: *mut LeanObject,
    mut v_url_5082_: *mut LeanObject,
    mut v_archiveFile_5083_: *mut LeanObject,
    mut v_headers_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_a_5088_: *mut LeanObject,
    mut v_a_5089_: *mut LeanObject,
    mut v_a_5090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5097_: u8 = 0;
    let mut v___y_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5099_: u8 = 0;
    let mut v___y_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: u8 = 0;
    let mut v___x_5106_: u8 = 0;
    let mut v_a_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5111_: u8 = 0;
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5116_: u8 = 0;
    let mut v_a_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut v_a_5128_: u8 = 0;
    let mut v_a_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildDir_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: u8 = 0;
    let mut v_log_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5137_: u8 = 0;
    let mut v_wantsRebuild_5138_: u8 = 0;
    let mut v_trace_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5142_: u8 = 0;
    let mut v_wantsRebuild_5143_: u8 = 0;
    let mut v_trace_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5149_: u8 = 0;
    let mut v_wantsRebuild_5150_: u8 = 0;
    let mut v_trace_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5155_: u8 = 0;
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceFile_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: u64 = 0;
    let mut v___x_5163_: u64 = 0;
    let mut v_depTrace_5164_: u64 = 0;
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: u8 = 0;
    let mut v___x_5174_: u8 = 0;
    let mut v___x_5175_: u8 = 0;
    let mut v___x_5176_: u8 = 0;
    let mut v___x_5177_: u8 = 0;
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: u8 = 0;
    let mut v_a_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_5148_ = lean_ctor_get(v_a_5090_, 0);
                v_action_5149_ = lean_ctor_get_uint8(
                    v_a_5090_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5150_ = lean_ctor_get_uint8(
                    v_a_5090_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_5151_ = lean_ctor_get(v_a_5090_, 1);
                v_buildTime_5152_ = lean_ctor_get(v_a_5090_, 2);
                v_isSharedCheck_5191_ = (!lean_is_exclusive(v_a_5090_)) as u8;
                if v_isSharedCheck_5191_ == 0 {
                    v___x_5154_ = v_a_5090_;
                    v_isShared_5155_ = v_isSharedCheck_5191_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_buildTime_5152_);
                    lean_inc(v_trace_5151_);
                    lean_inc(v_log_5148_);
                    lean_dec(v_a_5090_);
                    v___x_5154_ = lean_box(0);
                    v_isShared_5155_ = v_isSharedCheck_5191_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                v___x_5095_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5095_, 0, v_a_5093_);
                lean_ctor_set(v___x_5095_, 1, v_a_5094_);
                return v___x_5095_;
            }
            2 => {
                v___x_5103_ = 1;
                v___x_5104_ =
                    l_Lake_untar(v_archiveFile_5083_, v___y_5101_, v___x_5103_, v___y_5100_);
                v___x_5105_ = 3;
                v___x_5106_ = l_Lake_JobAction_merge(v___y_5099_, v___x_5105_);
                if lean_obj_tag(v___x_5104_) == 0 {
                    v_a_5107_ = lean_ctor_get(v___x_5104_, 0);
                    v_a_5108_ = lean_ctor_get(v___x_5104_, 1);
                    v_isSharedCheck_5116_ = (!lean_is_exclusive(v___x_5104_)) as u8;
                    if v_isSharedCheck_5116_ == 0 {
                        v___x_5110_ = v___x_5104_;
                        v_isShared_5111_ = v_isSharedCheck_5116_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5108_);
                        lean_inc(v_a_5107_);
                        lean_dec(v___x_5104_);
                        v___x_5110_ = lean_box(0);
                        v_isShared_5111_ = v_isSharedCheck_5116_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5117_ = lean_ctor_get(v___x_5104_, 0);
                    v_a_5118_ = lean_ctor_get(v___x_5104_, 1);
                    v_isSharedCheck_5126_ = (!lean_is_exclusive(v___x_5104_)) as u8;
                    if v_isSharedCheck_5126_ == 0 {
                        v___x_5120_ = v___x_5104_;
                        v_isShared_5121_ = v_isSharedCheck_5126_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5118_);
                        lean_inc(v_a_5117_);
                        lean_dec(v___x_5104_);
                        v___x_5120_ = lean_box(0);
                        v_isShared_5121_ = v_isSharedCheck_5126_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5112_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_5112_, 0, v_a_5108_);
                lean_ctor_set(v___x_5112_, 1, v___y_5098_);
                lean_ctor_set(v___x_5112_, 2, v___y_5102_);
                lean_ctor_set_uint8(
                    v___x_5112_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5106_,
                );
                lean_ctor_set_uint8(
                    v___x_5112_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___y_5097_,
                );
                if v_isShared_5111_ == 0 {
                    lean_ctor_set(v___x_5110_, 1, v___x_5112_);
                    v___x_5114_ = v___x_5110_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5107_);
                    lean_ctor_set(v_reuseFailAlloc_5115_, 1, v___x_5112_);
                    v___x_5114_ = v_reuseFailAlloc_5115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5114_;
            }
            5 => {
                v___x_5122_ = lean_alloc_ctor(0, 3, (2) as u32);
                lean_ctor_set(v___x_5122_, 0, v_a_5118_);
                lean_ctor_set(v___x_5122_, 1, v___y_5098_);
                lean_ctor_set(v___x_5122_, 2, v___y_5102_);
                lean_ctor_set_uint8(
                    v___x_5122_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5106_,
                );
                lean_ctor_set_uint8(
                    v___x_5122_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___y_5097_,
                );
                if v_isShared_5121_ == 0 {
                    lean_ctor_set(v___x_5120_, 1, v___x_5122_);
                    v___x_5124_ = v___x_5120_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5117_);
                    lean_ctor_set(v_reuseFailAlloc_5125_, 1, v___x_5122_);
                    v___x_5124_ = v_reuseFailAlloc_5125_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5124_;
            }
            7 => {
                v_config_5130_ = lean_ctor_get(v_self_5081_, 6);
                lean_inc_ref(v_config_5130_);
                v_dir_5131_ = lean_ctor_get(v_self_5081_, 4);
                lean_inc_ref(v_dir_5131_);
                lean_dec_ref(v_self_5081_);
                v_buildDir_5132_ = lean_ctor_get(v_config_5130_, 5);
                lean_inc_ref(v_buildDir_5132_);
                lean_dec_ref(v_config_5130_);
                v___x_5133_ = l_System_FilePath_normalize(v_buildDir_5132_);
                v___x_5134_ = l_Lake_joinRelative(v_dir_5131_, v___x_5133_);
                v___x_5135_ = l_System_FilePath_pathExists(v___x_5134_);
                if v_a_5128_ == 0 {
                    v_log_5136_ = lean_ctor_get(v_a_5129_, 0);
                    lean_inc_ref(v_log_5136_);
                    v_action_5137_ = lean_ctor_get_uint8(
                        v_a_5129_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_5138_ = lean_ctor_get_uint8(
                        v_a_5129_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_5139_ = lean_ctor_get(v_a_5129_, 1);
                    lean_inc_ref(v_trace_5139_);
                    v_buildTime_5140_ = lean_ctor_get(v_a_5129_, 2);
                    lean_inc(v_buildTime_5140_);
                    lean_dec_ref(v_a_5129_);
                    v___y_5097_ = v_wantsRebuild_5138_;
                    v___y_5098_ = v_trace_5139_;
                    v___y_5099_ = v_action_5137_;
                    v___y_5100_ = v_log_5136_;
                    v___y_5101_ = v___x_5134_;
                    v___y_5102_ = v_buildTime_5140_;
                    state = 2;
                    continue;
                } else {
                    if v___x_5135_ == 0 {
                        v_log_5141_ = lean_ctor_get(v_a_5129_, 0);
                        lean_inc_ref(v_log_5141_);
                        v_action_5142_ = lean_ctor_get_uint8(
                            v_a_5129_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_wantsRebuild_5143_ = lean_ctor_get_uint8(
                            v_a_5129_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_trace_5144_ = lean_ctor_get(v_a_5129_, 1);
                        lean_inc_ref(v_trace_5144_);
                        v_buildTime_5145_ = lean_ctor_get(v_a_5129_, 2);
                        lean_inc(v_buildTime_5145_);
                        lean_dec_ref(v_a_5129_);
                        v___y_5097_ = v_wantsRebuild_5143_;
                        v___y_5098_ = v_trace_5144_;
                        v___y_5099_ = v_action_5142_;
                        v___y_5100_ = v_log_5141_;
                        v___y_5101_ = v___x_5134_;
                        v___y_5102_ = v_buildTime_5145_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v___x_5134_);
                        lean_dec_ref(v_archiveFile_5083_);
                        v___x_5146_ = lean_box(0);
                        v___x_5147_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5147_, 0, v___x_5146_);
                        lean_ctor_set(v___x_5147_, 1, v_a_5129_);
                        return v___x_5147_;
                    }
                }
            }
            8 => {
                v___x_5156_ =
                    l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0;
                lean_inc_ref(v_archiveFile_5083_);
                v_traceFile_5157_ =
                    l_System_FilePath_addExtension(v_archiveFile_5083_, v___x_5156_);
                lean_inc_ref(v_traceFile_5157_);
                v___x_5158_ = l_Lake_readTraceFile(v_traceFile_5157_, v_log_5148_);
                if lean_obj_tag(v___x_5158_) == 0 {
                    v_a_5159_ = lean_ctor_get(v___x_5158_, 0);
                    lean_inc(v_a_5159_);
                    v_a_5160_ = lean_ctor_get(v___x_5158_, 1);
                    lean_inc(v_a_5160_);
                    lean_dec_ref_known(v___x_5158_, 2);
                    v___x_5161_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1;
                    v___x_5162_ = l_Lake_Hash_nil;
                    v___x_5163_ = lean_string_hash(v_url_5082_);
                    v_depTrace_5164_ = lean_uint64_mix_hash(v___x_5162_, v___x_5163_);
                    v___x_5165_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2;
                    v___x_5166_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once), _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
                    v___x_5167_ = lean_alloc_ctor(0, 3, (8) as u32);
                    lean_ctor_set(v___x_5167_, 0, v___x_5165_);
                    lean_ctor_set(v___x_5167_, 1, v___x_5161_);
                    lean_ctor_set(v___x_5167_, 2, v___x_5166_);
                    lean_ctor_set_uint64(
                        v___x_5167_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_depTrace_5164_,
                    );
                    if v_isShared_5155_ == 0 {
                        lean_ctor_set(v___x_5154_, 0, v_a_5160_);
                        v___x_5169_ = v___x_5154_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_5185_ = lean_alloc_ctor(0, 3, (2) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5160_);
                        lean_ctor_set(v_reuseFailAlloc_5185_, 1, v_trace_5151_);
                        lean_ctor_set(v_reuseFailAlloc_5185_, 2, v_buildTime_5152_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_5185_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_action_5149_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_5185_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_wantsRebuild_5150_,
                        );
                        v___x_5169_ = v_reuseFailAlloc_5185_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_traceFile_5157_);
                    lean_dec_ref(v_archiveFile_5083_);
                    lean_dec_ref(v_url_5082_);
                    lean_dec_ref(v_self_5081_);
                    v_a_5186_ = lean_ctor_get(v___x_5158_, 0);
                    lean_inc(v_a_5186_);
                    v_a_5187_ = lean_ctor_get(v___x_5158_, 1);
                    lean_inc(v_a_5187_);
                    lean_dec_ref_known(v___x_5158_, 2);
                    if v_isShared_5155_ == 0 {
                        lean_ctor_set(v___x_5154_, 0, v_a_5187_);
                        v___x_5189_ = v___x_5154_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 3, (2) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5187_);
                        lean_ctor_set(v_reuseFailAlloc_5190_, 1, v_trace_5151_);
                        lean_ctor_set(v_reuseFailAlloc_5190_, 2, v_buildTime_5152_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_5190_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_action_5149_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_5190_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v_wantsRebuild_5150_,
                        );
                        v___x_5189_ = v_reuseFailAlloc_5190_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                v___x_5170_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_5085_, v_archiveFile_5083_, v___x_5167_, v_a_5159_, v___x_5166_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v___x_5169_);
                if lean_obj_tag(v___x_5170_) == 0 {
                    v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
                    lean_inc(v_a_5171_);
                    v_a_5172_ = lean_ctor_get(v___x_5170_, 1);
                    lean_inc(v_a_5172_);
                    lean_dec_ref_known(v___x_5170_, 2);
                    v___x_5173_ = 0;
                    v___x_5174_ = (lean_unbox(v_a_5171_) as u8);
                    lean_dec(v_a_5171_);
                    v___x_5175_ = l_Lake_instDecidableEqOutputStatus(v___x_5174_, v___x_5173_);
                    if v___x_5175_ == 0 {
                        lean_dec_ref_known(v___x_5167_, 3);
                        lean_dec_ref(v_traceFile_5157_);
                        lean_dec_ref(v_url_5082_);
                        v___x_5176_ = 1;
                        v_a_5128_ = v___x_5176_;
                        v_a_5129_ = v_a_5172_;
                        state = 7;
                        continue;
                    } else {
                        v___x_5177_ = 4;
                        lean_inc_ref(v_archiveFile_5083_);
                        v___x_5178_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_5082_, v_archiveFile_5083_, v_headers_5084_, v___x_5167_, v_traceFile_5157_, v___x_5177_, v_a_5089_, v_a_5172_);
                        lean_dec_ref_known(v___x_5167_, 3);
                        if lean_obj_tag(v___x_5178_) == 0 {
                            v_a_5179_ = lean_ctor_get(v___x_5178_, 1);
                            lean_inc(v_a_5179_);
                            lean_dec_ref_known(v___x_5178_, 2);
                            v___x_5180_ = 0;
                            v_a_5128_ = v___x_5180_;
                            v_a_5129_ = v_a_5179_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec_ref(v_archiveFile_5083_);
                            lean_dec_ref(v_self_5081_);
                            v_a_5181_ = lean_ctor_get(v___x_5178_, 0);
                            lean_inc(v_a_5181_);
                            v_a_5182_ = lean_ctor_get(v___x_5178_, 1);
                            lean_inc(v_a_5182_);
                            lean_dec_ref_known(v___x_5178_, 2);
                            v_a_5093_ = v_a_5181_;
                            v_a_5094_ = v_a_5182_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_5167_, 3);
                    lean_dec_ref(v_traceFile_5157_);
                    lean_dec_ref(v_archiveFile_5083_);
                    lean_dec_ref(v_url_5082_);
                    lean_dec_ref(v_self_5081_);
                    v_a_5183_ = lean_ctor_get(v___x_5170_, 0);
                    lean_inc(v_a_5183_);
                    v_a_5184_ = lean_ctor_get(v___x_5170_, 1);
                    lean_inc(v_a_5184_);
                    lean_dec_ref_known(v___x_5170_, 2);
                    v_a_5093_ = v_a_5183_;
                    v_a_5094_ = v_a_5184_;
                    state = 1;
                    continue;
                }
            }
            10 => {
                v_a_5093_ = v_a_5186_;
                v_a_5094_ = v___x_5189_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(
    mut v_self_5192_: *mut LeanObject,
    mut v_url_5193_: *mut LeanObject,
    mut v_archiveFile_5194_: *mut LeanObject,
    mut v_headers_5195_: *mut LeanObject,
    mut v_a_5196_: *mut LeanObject,
    mut v_a_5197_: *mut LeanObject,
    mut v_a_5198_: *mut LeanObject,
    mut v_a_5199_: *mut LeanObject,
    mut v_a_5200_: *mut LeanObject,
    mut v_a_5201_: *mut LeanObject,
    mut v_a_5202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5203_: *mut LeanObject = core::ptr::null_mut();
    v_res_5203_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(
        v_self_5192_,
        v_url_5193_,
        v_archiveFile_5194_,
        v_headers_5195_,
        v_a_5196_,
        v_a_5197_,
        v_a_5198_,
        v_a_5199_,
        v_a_5200_,
        v_a_5201_,
    );
    lean_dec_ref(v_a_5200_);
    lean_dec(v_a_5199_);
    lean_dec(v_a_5198_);
    lean_dec(v_a_5197_);
    lean_dec_ref(v_a_5196_);
    lean_dec_ref(v_headers_5195_);
    return v_res_5203_;
}
pub unsafe fn l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(
    mut v_a_5204_: *mut LeanObject,
    mut v_info_5205_: *mut LeanObject,
    mut v_depTrace_5206_: *mut LeanObject,
    mut v_depHash_5207_: *mut LeanObject,
    mut v_oldTrace_5208_: *mut LeanObject,
    mut v_a_5209_: *mut LeanObject,
    mut v_a_5210_: *mut LeanObject,
    mut v_a_5211_: *mut LeanObject,
    mut v_a_5212_: *mut LeanObject,
    mut v_a_5213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    v___x_5215_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_5205_, v_depTrace_5206_, v_depHash_5207_, v_oldTrace_5208_, v_a_5212_, v_a_5213_);
    return v___x_5215_;
}
pub unsafe fn l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(
    mut v_a_5216_: *mut LeanObject,
    mut v_info_5217_: *mut LeanObject,
    mut v_depTrace_5218_: *mut LeanObject,
    mut v_depHash_5219_: *mut LeanObject,
    mut v_oldTrace_5220_: *mut LeanObject,
    mut v_a_5221_: *mut LeanObject,
    mut v_a_5222_: *mut LeanObject,
    mut v_a_5223_: *mut LeanObject,
    mut v_a_5224_: *mut LeanObject,
    mut v_a_5225_: *mut LeanObject,
    mut v_a_5226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5227_: *mut LeanObject = core::ptr::null_mut();
    v_res_5227_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_5216_, v_info_5217_, v_depTrace_5218_, v_depHash_5219_, v_oldTrace_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
    lean_dec_ref(v_a_5224_);
    lean_dec(v_a_5223_);
    lean_dec(v_a_5222_);
    lean_dec(v_a_5221_);
    lean_dec_ref(v_oldTrace_5220_);
    lean_dec(v_depHash_5219_);
    lean_dec_ref(v_depTrace_5218_);
    lean_dec_ref(v_info_5217_);
    lean_dec_ref(v_a_5216_);
    return v_res_5227_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(
    mut v_getUrl_5228_: *mut LeanObject,
    mut v_pkg_5229_: *mut LeanObject,
    mut v_archiveFile_5230_: *mut LeanObject,
    mut v_headers_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
    mut v___y_5237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_5240_: u8 = 0;
    let mut v___y_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5247_: u8 = 0;
    let mut v_wantsRebuild_5248_: u8 = 0;
    let mut v_trace_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5253_: u8 = 0;
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: u8 = 0;
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: u8 = 0;
    let mut v_reuseFailAlloc_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5260_: u8 = 0;
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: u8 = 0;
    let mut v_a_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___y_5236_);
                lean_inc(v___y_5235_);
                lean_inc(v___y_5234_);
                lean_inc(v___y_5233_);
                lean_inc_ref(v___y_5232_);
                lean_inc_ref(v_pkg_5229_);
                v___x_5261_ = lean_apply_8(
                    v_getUrl_5228_,
                    v_pkg_5229_,
                    v___y_5232_,
                    v___y_5233_,
                    v___y_5234_,
                    v___y_5235_,
                    v___y_5236_,
                    v___y_5237_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5261_) == 0 {
                    v_a_5262_ = lean_ctor_get(v___x_5261_, 0);
                    lean_inc(v_a_5262_);
                    v_a_5263_ = lean_ctor_get(v___x_5261_, 1);
                    lean_inc(v_a_5263_);
                    lean_dec_ref_known(v___x_5261_, 2);
                    lean_inc_ref(v_pkg_5229_);
                    v___x_5264_ = lean_apply_1(v_archiveFile_5230_, v_pkg_5229_);
                    v___x_5265_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(
                        v_pkg_5229_,
                        v_a_5262_,
                        v___x_5264_,
                        v_headers_5231_,
                        v___y_5232_,
                        v___y_5233_,
                        v___y_5234_,
                        v___y_5235_,
                        v___y_5236_,
                        v_a_5263_,
                    );
                    lean_dec_ref(v___y_5232_);
                    if lean_obj_tag(v___x_5265_) == 0 {
                        v_a_5266_ = lean_ctor_get(v___x_5265_, 1);
                        lean_inc(v_a_5266_);
                        lean_dec_ref_known(v___x_5265_, 2);
                        v___x_5267_ = 1;
                        v_r_5240_ = v___x_5267_;
                        v___y_5241_ = v_a_5266_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5268_ = lean_ctor_get(v___x_5265_, 1);
                        lean_inc(v_a_5268_);
                        lean_dec_ref_known(v___x_5265_, 2);
                        v_a_5245_ = v_a_5268_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_5232_);
                    lean_dec_ref(v_archiveFile_5230_);
                    lean_dec_ref(v_pkg_5229_);
                    v_a_5269_ = lean_ctor_get(v___x_5261_, 1);
                    lean_inc(v_a_5269_);
                    lean_dec_ref_known(v___x_5261_, 2);
                    v_a_5245_ = v_a_5269_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5242_ = lean_box((v_r_5240_) as usize);
                v___x_5243_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5243_, 0, v___x_5242_);
                lean_ctor_set(v___x_5243_, 1, v___y_5241_);
                return v___x_5243_;
            }
            2 => {
                v_log_5246_ = lean_ctor_get(v_a_5245_, 0);
                v_action_5247_ = lean_ctor_get_uint8(
                    v_a_5245_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5248_ = lean_ctor_get_uint8(
                    v_a_5245_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_5249_ = lean_ctor_get(v_a_5245_, 1);
                v_buildTime_5250_ = lean_ctor_get(v_a_5245_, 2);
                v_isSharedCheck_5260_ = (!lean_is_exclusive(v_a_5245_)) as u8;
                if v_isSharedCheck_5260_ == 0 {
                    v___x_5252_ = v_a_5245_;
                    v_isShared_5253_ = v_isSharedCheck_5260_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_buildTime_5250_);
                    lean_inc(v_trace_5249_);
                    lean_inc(v_log_5246_);
                    lean_dec(v_a_5245_);
                    v___x_5252_ = lean_box(0);
                    v_isShared_5253_ = v_isSharedCheck_5260_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5254_ = 4;
                v___x_5255_ = l_Lake_JobAction_merge(v_action_5247_, v___x_5254_);
                if v_isShared_5253_ == 0 {
                    v___x_5257_ = v___x_5252_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5259_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5259_, 0, v_log_5246_);
                    lean_ctor_set(v_reuseFailAlloc_5259_, 1, v_trace_5249_);
                    lean_ctor_set(v_reuseFailAlloc_5259_, 2, v_buildTime_5250_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5259_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5248_,
                    );
                    v___x_5257_ = v_reuseFailAlloc_5259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_5257_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5255_,
                );
                v___x_5258_ = 0;
                v_r_5240_ = v___x_5258_;
                v___y_5241_ = v___x_5257_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(
    mut v_getUrl_5270_: *mut LeanObject,
    mut v_pkg_5271_: *mut LeanObject,
    mut v_archiveFile_5272_: *mut LeanObject,
    mut v_headers_5273_: *mut LeanObject,
    mut v___y_5274_: *mut LeanObject,
    mut v___y_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5281_: *mut LeanObject = core::ptr::null_mut();
    v_res_5281_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_5270_, v_pkg_5271_, v_archiveFile_5272_, v_headers_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
    lean_dec_ref(v___y_5278_);
    lean_dec(v___y_5277_);
    lean_dec(v___y_5276_);
    lean_dec(v___y_5275_);
    lean_dec_ref(v_headers_5273_);
    return v_res_5281_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(
    mut v_getUrl_5282_: *mut LeanObject,
    mut v_archiveFile_5283_: *mut LeanObject,
    mut v_headers_5284_: *mut LeanObject,
    mut v___x_5285_: *mut LeanObject,
    mut v_facet_5286_: *mut LeanObject,
    mut v_pkg_5287_: *mut LeanObject,
    mut v___y_5288_: *mut LeanObject,
    mut v___y_5289_: *mut LeanObject,
    mut v___y_5290_: *mut LeanObject,
    mut v___y_5291_: *mut LeanObject,
    mut v___y_5292_: *mut LeanObject,
    mut v___y_5293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v_task_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5311_: u8 = 0;
    let mut v_registeredJobs_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: u8 = 0;
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5332_: u8 = 0;
    let mut v_unused_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_pkg_5287_);
                v___f_5295_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
                lean_closure_set(v___f_5295_, 0, v_getUrl_5282_);
                lean_closure_set(v___f_5295_, 1, v_pkg_5287_);
                lean_closure_set(v___f_5295_, 2, v_archiveFile_5283_);
                lean_closure_set(v___f_5295_, 3, v_headers_5284_);
                v___x_5296_ = lean_unsigned_to_nat(0);
                v___x_5297_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                lean_inc(v___x_5285_);
                v___x_5298_ =
                    lean_alloc_closure(l_Lake_Job_async___boxed as *mut core::ffi::c_void, 12, 5);
                lean_closure_set(v___x_5298_, 0, lean_box(0));
                lean_closure_set(v___x_5298_, 1, v___x_5285_);
                lean_closure_set(v___x_5298_, 2, v___f_5295_);
                lean_closure_set(v___x_5298_, 3, v___x_5296_);
                lean_closure_set(v___x_5298_, 4, v___x_5297_);
                v___x_5299_ = lean_alloc_closure(
                    l_Lake_JobM_runSpawnM___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                lean_closure_set(v___x_5299_, 0, lean_box(0));
                lean_closure_set(v___x_5299_, 1, v___x_5298_);
                v___x_5300_ = lean_alloc_closure(
                    l_Lake_FetchM_runJobM___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                lean_closure_set(v___x_5300_, 0, lean_box(0));
                lean_closure_set(v___x_5300_, 1, v___x_5299_);
                v___x_5301_ = l_Lake_ensureJob___redArg(
                    v___x_5285_,
                    v___x_5300_,
                    v___y_5288_,
                    v___y_5289_,
                    v___y_5290_,
                    v___y_5291_,
                    v___y_5292_,
                    v___y_5293_,
                );
                if lean_obj_tag(v___x_5301_) == 0 {
                    v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
                    v_a_5303_ = lean_ctor_get(v___x_5301_, 1);
                    v_isSharedCheck_5334_ = (!lean_is_exclusive(v___x_5301_)) as u8;
                    if v_isSharedCheck_5334_ == 0 {
                        v___x_5305_ = v___x_5301_;
                        v_isShared_5306_ = v_isSharedCheck_5334_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5303_);
                        lean_inc(v_a_5302_);
                        lean_dec(v___x_5301_);
                        v___x_5305_ = lean_box(0);
                        v_isShared_5306_ = v_isSharedCheck_5334_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pkg_5287_);
                    lean_dec(v_facet_5286_);
                    return v___x_5301_;
                }
            }
            1 => {
                v_task_5307_ = lean_ctor_get(v_a_5302_, 0);
                v_kind_5308_ = lean_ctor_get(v_a_5302_, 1);
                v_isSharedCheck_5332_ = (!lean_is_exclusive(v_a_5302_)) as u8;
                if v_isSharedCheck_5332_ == 0 {
                    v_unused_5333_ = lean_ctor_get(v_a_5302_, 2);
                    lean_dec(v_unused_5333_);
                    v___x_5310_ = v_a_5302_;
                    v_isShared_5311_ = v_isSharedCheck_5332_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_5308_);
                    lean_inc(v_task_5307_);
                    lean_dec(v_a_5302_);
                    v___x_5310_ = lean_box(0);
                    v_isShared_5311_ = v_isSharedCheck_5332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_5312_ = lean_ctor_get(v___y_5292_, 3);
                v___x_5313_ = lean_st_ref_take(v_registeredJobs_5312_);
                v_baseName_5314_ = lean_ctor_get(v_pkg_5287_, 1);
                lean_inc(v_baseName_5314_);
                lean_dec_ref(v_pkg_5287_);
                v___x_5315_ = 1;
                v___x_5316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_5314_,
                    v___x_5315_,
                );
                v___x_5317_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                v___x_5318_ = lean_string_append(v___x_5316_, v___x_5317_);
                v___x_5319_ = l_Lake_Name_eraseHead(v_facet_5286_);
                v___x_5320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_5319_,
                    v___x_5315_,
                );
                v___x_5321_ = lean_string_append(v___x_5318_, v___x_5320_);
                lean_dec_ref(v___x_5320_);
                if v_isShared_5311_ == 0 {
                    lean_ctor_set(v___x_5310_, 2, v___x_5321_);
                    v_job_5323_ = v___x_5310_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_task_5307_);
                    lean_ctor_set(v_reuseFailAlloc_5331_, 1, v_kind_5308_);
                    lean_ctor_set(v_reuseFailAlloc_5331_, 2, v___x_5321_);
                    v_job_5323_ = v_reuseFailAlloc_5331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_5323_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5315_,
                );
                lean_inc_ref(v_job_5323_);
                v___x_5324_ = l_Lake_Job_toOpaque___redArg(v_job_5323_);
                v___x_5325_ = lean_array_push(v___x_5313_, v___x_5324_);
                v___x_5326_ = lean_st_ref_set(v_registeredJobs_5312_, v___x_5325_);
                v___x_5327_ = l_Lake_Job_renew___redArg(v_job_5323_);
                if v_isShared_5306_ == 0 {
                    lean_ctor_set(v___x_5305_, 0, v___x_5327_);
                    v___x_5329_ = v___x_5305_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5330_, 0, v___x_5327_);
                    lean_ctor_set(v_reuseFailAlloc_5330_, 1, v_a_5303_);
                    v___x_5329_ = v_reuseFailAlloc_5330_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(
    mut v_getUrl_5335_: *mut LeanObject,
    mut v_archiveFile_5336_: *mut LeanObject,
    mut v_headers_5337_: *mut LeanObject,
    mut v___x_5338_: *mut LeanObject,
    mut v_facet_5339_: *mut LeanObject,
    mut v_pkg_5340_: *mut LeanObject,
    mut v___y_5341_: *mut LeanObject,
    mut v___y_5342_: *mut LeanObject,
    mut v___y_5343_: *mut LeanObject,
    mut v___y_5344_: *mut LeanObject,
    mut v___y_5345_: *mut LeanObject,
    mut v___y_5346_: *mut LeanObject,
    mut v___y_5347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5348_: *mut LeanObject = core::ptr::null_mut();
    v_res_5348_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_5335_, v_archiveFile_5336_, v_headers_5337_, v___x_5338_, v_facet_5339_, v_pkg_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
    lean_dec_ref(v___y_5345_);
    lean_dec(v___y_5344_);
    lean_dec(v___y_5343_);
    lean_dec(v___y_5342_);
    return v_res_5348_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(
    mut v_facet_5356_: *mut LeanObject,
    mut v_archiveFile_5357_: *mut LeanObject,
    mut v_getUrl_5358_: *mut LeanObject,
    mut v_headers_5359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: u8 = 0;
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    v___x_5360_ = l_Lake_instDataKindBool;
    v___f_5361_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed as *mut core::ffi::c_void, 13, 5);
    lean_closure_set(v___f_5361_, 0, v_getUrl_5358_);
    lean_closure_set(v___f_5361_, 1, v_archiveFile_5357_);
    lean_closure_set(v___f_5361_, 2, v_headers_5359_);
    lean_closure_set(v___f_5361_, 3, v___x_5360_);
    lean_closure_set(v___f_5361_, 4, v_facet_5356_);
    v___x_5362_ = l_Lake_Package_keyword;
    v___x_5363_ = 1;
    v___x_5364_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3;
    v___x_5365_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_5365_, 0, v___x_5362_);
    lean_ctor_set(v___x_5365_, 1, v___f_5361_);
    lean_ctor_set(v___x_5365_, 2, v___x_5360_);
    lean_ctor_set(v___x_5365_, 3, v___x_5364_);
    lean_ctor_set_uint8(
        v___x_5365_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_5363_,
    );
    lean_ctor_set_uint8(
        v___x_5365_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_5363_,
    );
    return v___x_5365_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(
    mut v_facet_5366_: *mut LeanObject,
    mut v_archiveFile_5367_: *mut LeanObject,
    mut v_getUrl_5368_: *mut LeanObject,
    mut v_headers_5369_: *mut LeanObject,
    mut v_inst_5370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: u8 = 0;
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    v___x_5371_ = l_Lake_instDataKindBool;
    v___f_5372_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed as *mut core::ffi::c_void, 13, 5);
    lean_closure_set(v___f_5372_, 0, v_getUrl_5368_);
    lean_closure_set(v___f_5372_, 1, v_archiveFile_5367_);
    lean_closure_set(v___f_5372_, 2, v_headers_5369_);
    lean_closure_set(v___f_5372_, 3, v___x_5371_);
    lean_closure_set(v___f_5372_, 4, v_facet_5366_);
    v___x_5373_ = l_Lake_Package_keyword;
    v___x_5374_ = 1;
    v___x_5375_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3;
    v___x_5376_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_5376_, 0, v___x_5373_);
    lean_ctor_set(v___x_5376_, 1, v___f_5372_);
    lean_ctor_set(v___x_5376_, 2, v___x_5371_);
    lean_ctor_set(v___x_5376_, 3, v___x_5375_);
    lean_ctor_set_uint8(
        v___x_5376_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_5374_,
    );
    lean_ctor_set_uint8(
        v___x_5376_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_5374_,
    );
    return v___x_5376_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(
    mut v_what_5378_: *mut LeanObject,
    mut v_baseName_5379_: *mut LeanObject,
    mut v_optFacet_5380_: *mut LeanObject,
    mut v_success_5381_: u8,
    mut v___y_5382_: *mut LeanObject,
    mut v___y_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
    mut v___y_5386_: *mut LeanObject,
    mut v___y_5387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5393_: u8 = 0;
    let mut v_wantsRebuild_5394_: u8 = 0;
    let mut v_trace_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: u8 = 0;
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5411_: u8 = 0;
    let mut v_toBuildConfig_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_5413_: u8 = 0;
    let mut v___x_5414_: u8 = 0;
    let mut v___x_5415_: u8 = 0;
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_success_5381_ == 0 {
                    v_toBuildConfig_5412_ = lean_ctor_get(v___y_5386_, 0);
                    v_verbosity_5413_ = lean_ctor_get_uint8(
                        v_toBuildConfig_5412_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v___x_5414_ = 2;
                    v___x_5415_ = l_Lake_instDecidableEqVerbosity(v_verbosity_5413_, v___x_5414_);
                    if v___x_5415_ == 0 {
                        lean_dec(v_optFacet_5380_);
                        lean_dec(v_baseName_5379_);
                        v___x_5416_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
                        v_a_5390_ = v___x_5416_;
                        v_a_5391_ = v___y_5387_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5417_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
                        v___x_5418_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_baseName_5379_,
                                v___x_5415_,
                            );
                        v___x_5419_ = lean_string_append(v___x_5417_, v___x_5418_);
                        lean_dec_ref(v___x_5418_);
                        v___x_5420_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                        v___x_5421_ = lean_string_append(v___x_5419_, v___x_5420_);
                        v___x_5422_ = l_Lake_Name_eraseHead(v_optFacet_5380_);
                        v___x_5423_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_5422_,
                                v___x_5415_,
                            );
                        v___x_5424_ = lean_string_append(v___x_5421_, v___x_5423_);
                        lean_dec_ref(v___x_5423_);
                        v___x_5425_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
                        v___x_5426_ = lean_string_append(v___x_5424_, v___x_5425_);
                        v_a_5390_ = v___x_5426_;
                        v_a_5391_ = v___y_5387_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_optFacet_5380_);
                    lean_dec(v_baseName_5379_);
                    v___x_5427_ = lean_box(0);
                    v___x_5428_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5428_, 0, v___x_5427_);
                    lean_ctor_set(v___x_5428_, 1, v___y_5387_);
                    return v___x_5428_;
                }
            }
            1 => {
                v_log_5392_ = lean_ctor_get(v_a_5391_, 0);
                v_action_5393_ = lean_ctor_get_uint8(
                    v_a_5391_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5394_ = lean_ctor_get_uint8(
                    v_a_5391_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_5395_ = lean_ctor_get(v_a_5391_, 1);
                v_buildTime_5396_ = lean_ctor_get(v_a_5391_, 2);
                v_isSharedCheck_5411_ = (!lean_is_exclusive(v_a_5391_)) as u8;
                if v_isSharedCheck_5411_ == 0 {
                    v___x_5398_ = v_a_5391_;
                    v_isShared_5399_ = v_isSharedCheck_5411_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_buildTime_5396_);
                    lean_inc(v_trace_5395_);
                    lean_inc(v_log_5392_);
                    lean_dec(v_a_5391_);
                    v___x_5398_ = lean_box(0);
                    v_isShared_5399_ = v_isSharedCheck_5411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5400_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0;
                v___x_5401_ = lean_string_append(v___x_5400_, v_what_5378_);
                v___x_5402_ = lean_string_append(v___x_5401_, v_a_5390_);
                lean_dec_ref(v_a_5390_);
                v___x_5403_ = 3;
                v___x_5404_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5404_, 0, v___x_5402_);
                lean_ctor_set_uint8(
                    v___x_5404_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5403_,
                );
                v___x_5405_ = lean_array_get_size(v_log_5392_);
                v___x_5406_ = lean_array_push(v_log_5392_, v___x_5404_);
                if v_isShared_5399_ == 0 {
                    lean_ctor_set(v___x_5398_, 0, v___x_5406_);
                    v___x_5408_ = v___x_5398_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5410_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5406_);
                    lean_ctor_set(v_reuseFailAlloc_5410_, 1, v_trace_5395_);
                    lean_ctor_set(v_reuseFailAlloc_5410_, 2, v_buildTime_5396_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5410_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5393_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5410_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5394_,
                    );
                    v___x_5408_ = v_reuseFailAlloc_5410_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5409_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5409_, 0, v___x_5405_);
                lean_ctor_set(v___x_5409_, 1, v___x_5408_);
                return v___x_5409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(
    mut v_what_5429_: *mut LeanObject,
    mut v_baseName_5430_: *mut LeanObject,
    mut v_optFacet_5431_: *mut LeanObject,
    mut v_success_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
    mut v___y_5437_: *mut LeanObject,
    mut v___y_5438_: *mut LeanObject,
    mut v___y_5439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_success_boxed_5440_: u8 = 0;
    let mut v_res_5441_: *mut LeanObject = core::ptr::null_mut();
    v_success_boxed_5440_ = (lean_unbox(v_success_5432_) as u8);
    v_res_5441_ =
        l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(
            v_what_5429_,
            v_baseName_5430_,
            v_optFacet_5431_,
            v_success_boxed_5440_,
            v___y_5433_,
            v___y_5434_,
            v___y_5435_,
            v___y_5436_,
            v___y_5437_,
            v___y_5438_,
        );
    lean_dec_ref(v___y_5437_);
    lean_dec(v___y_5436_);
    lean_dec(v___y_5435_);
    lean_dec(v___y_5434_);
    lean_dec_ref(v___y_5433_);
    lean_dec_ref(v_what_5429_);
    return v_res_5441_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(
    mut v___x_5442_: *mut LeanObject,
    mut v___x_5443_: *mut LeanObject,
    mut v___f_5444_: *mut LeanObject,
    mut v___y_5445_: *mut LeanObject,
    mut v___y_5446_: *mut LeanObject,
    mut v___y_5447_: *mut LeanObject,
    mut v___y_5448_: *mut LeanObject,
    mut v___y_5449_: *mut LeanObject,
    mut v___y_5450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5457_: u8 = 0;
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: u8 = 0;
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5465_: u8 = 0;
    let mut v_a_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5470_: u8 = 0;
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___y_5445_);
                lean_inc_ref(v___y_5449_);
                lean_inc(v___y_5448_);
                lean_inc(v___y_5447_);
                lean_inc(v___y_5446_);
                v___x_5452_ = lean_apply_7(
                    v___y_5445_,
                    v___x_5442_,
                    v___y_5446_,
                    v___y_5447_,
                    v___y_5448_,
                    v___y_5449_,
                    v___y_5450_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5452_) == 0 {
                    v_a_5453_ = lean_ctor_get(v___x_5452_, 0);
                    v_a_5454_ = lean_ctor_get(v___x_5452_, 1);
                    v_isSharedCheck_5465_ = (!lean_is_exclusive(v___x_5452_)) as u8;
                    if v_isSharedCheck_5465_ == 0 {
                        v___x_5456_ = v___x_5452_;
                        v_isShared_5457_ = v_isSharedCheck_5465_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5454_);
                        lean_inc(v_a_5453_);
                        lean_dec(v___x_5452_);
                        v___x_5456_ = lean_box(0);
                        v_isShared_5457_ = v_isSharedCheck_5465_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_5445_);
                    lean_dec_ref(v___f_5444_);
                    lean_dec(v___x_5443_);
                    v_a_5466_ = lean_ctor_get(v___x_5452_, 0);
                    v_a_5467_ = lean_ctor_get(v___x_5452_, 1);
                    v_isSharedCheck_5474_ = (!lean_is_exclusive(v___x_5452_)) as u8;
                    if v_isSharedCheck_5474_ == 0 {
                        v___x_5469_ = v___x_5452_;
                        v_isShared_5470_ = v_isSharedCheck_5474_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5467_);
                        lean_inc(v_a_5466_);
                        lean_dec(v___x_5452_);
                        v___x_5469_ = lean_box(0);
                        v_isShared_5470_ = v_isSharedCheck_5474_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5458_ = lean_unsigned_to_nat(0);
                v___x_5459_ = 0;
                v___x_5460_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                v___x_5461_ = l_Lake_Job_mapM___redArg(
                    v___x_5443_,
                    v_a_5453_,
                    v___f_5444_,
                    v___x_5458_,
                    v___x_5459_,
                    v___y_5445_,
                    v___y_5446_,
                    v___y_5447_,
                    v___y_5448_,
                    v___y_5449_,
                    v___x_5460_,
                );
                if v_isShared_5457_ == 0 {
                    lean_ctor_set(v___x_5456_, 0, v___x_5461_);
                    v___x_5463_ = v___x_5456_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___x_5461_);
                    lean_ctor_set(v_reuseFailAlloc_5464_, 1, v_a_5454_);
                    v___x_5463_ = v_reuseFailAlloc_5464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5463_;
            }
            3 => {
                if v_isShared_5470_ == 0 {
                    v___x_5472_ = v___x_5469_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5473_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_a_5466_);
                    lean_ctor_set(v_reuseFailAlloc_5473_, 1, v_a_5467_);
                    v___x_5472_ = v_reuseFailAlloc_5473_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(
    mut v___x_5475_: *mut LeanObject,
    mut v___x_5476_: *mut LeanObject,
    mut v___f_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5485_: *mut LeanObject = core::ptr::null_mut();
    v_res_5485_ =
        l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(
            v___x_5475_,
            v___x_5476_,
            v___f_5477_,
            v___y_5478_,
            v___y_5479_,
            v___y_5480_,
            v___y_5481_,
            v___y_5482_,
            v___y_5483_,
        );
    lean_dec_ref(v___y_5482_);
    lean_dec(v___y_5481_);
    lean_dec(v___y_5480_);
    lean_dec(v___y_5479_);
    return v_res_5485_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(
    mut v_what_5486_: *mut LeanObject,
    mut v_optFacet_5487_: *mut LeanObject,
    mut v___x_5488_: *mut LeanObject,
    mut v_facet_5489_: *mut LeanObject,
    mut v_pkg_5490_: *mut LeanObject,
    mut v___y_5491_: *mut LeanObject,
    mut v___y_5492_: *mut LeanObject,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_baseName_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v_task_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5515_: u8 = 0;
    let mut v_registeredJobs_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: u8 = 0;
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: u8 = 0;
    let mut v_job_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_unused_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_baseName_5498_ = lean_ctor_get(v_pkg_5490_, 1);
                lean_inc_n(v_baseName_5498_, 2);
                v_keyName_5499_ = lean_ctor_get(v_pkg_5490_, 2);
                lean_inc(v_optFacet_5487_);
                v___f_5500_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 3);
                lean_closure_set(v___f_5500_, 0, v_what_5486_);
                lean_closure_set(v___f_5500_, 1, v_baseName_5498_);
                lean_closure_set(v___f_5500_, 2, v_optFacet_5487_);
                lean_inc(v_keyName_5499_);
                v___x_5501_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5501_, 0, v_keyName_5499_);
                v___x_5502_ = l_Lake_Package_keyword;
                v___x_5503_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_5503_, 0, v___x_5501_);
                lean_ctor_set(v___x_5503_, 1, v___x_5502_);
                lean_ctor_set(v___x_5503_, 2, v_pkg_5490_);
                lean_ctor_set(v___x_5503_, 3, v_optFacet_5487_);
                lean_inc(v___x_5488_);
                v___f_5504_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_5504_, 0, v___x_5503_);
                lean_closure_set(v___f_5504_, 1, v___x_5488_);
                lean_closure_set(v___f_5504_, 2, v___f_5500_);
                v___x_5505_ = l_Lake_ensureJob___redArg(
                    v___x_5488_,
                    v___f_5504_,
                    v___y_5491_,
                    v___y_5492_,
                    v___y_5493_,
                    v___y_5494_,
                    v___y_5495_,
                    v___y_5496_,
                );
                if lean_obj_tag(v___x_5505_) == 0 {
                    v_a_5506_ = lean_ctor_get(v___x_5505_, 0);
                    v_a_5507_ = lean_ctor_get(v___x_5505_, 1);
                    v_isSharedCheck_5538_ = (!lean_is_exclusive(v___x_5505_)) as u8;
                    if v_isSharedCheck_5538_ == 0 {
                        v___x_5509_ = v___x_5505_;
                        v_isShared_5510_ = v_isSharedCheck_5538_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5507_);
                        lean_inc(v_a_5506_);
                        lean_dec(v___x_5505_);
                        v___x_5509_ = lean_box(0);
                        v_isShared_5510_ = v_isSharedCheck_5538_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_baseName_5498_);
                    lean_dec(v_facet_5489_);
                    return v___x_5505_;
                }
            }
            1 => {
                v_task_5511_ = lean_ctor_get(v_a_5506_, 0);
                v_kind_5512_ = lean_ctor_get(v_a_5506_, 1);
                v_isSharedCheck_5536_ = (!lean_is_exclusive(v_a_5506_)) as u8;
                if v_isSharedCheck_5536_ == 0 {
                    v_unused_5537_ = lean_ctor_get(v_a_5506_, 2);
                    lean_dec(v_unused_5537_);
                    v___x_5514_ = v_a_5506_;
                    v_isShared_5515_ = v_isSharedCheck_5536_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_5512_);
                    lean_inc(v_task_5511_);
                    lean_dec(v_a_5506_);
                    v___x_5514_ = lean_box(0);
                    v_isShared_5515_ = v_isSharedCheck_5536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_5516_ = lean_ctor_get(v___y_5495_, 3);
                v___x_5517_ = lean_st_ref_take(v_registeredJobs_5516_);
                v___x_5518_ = 1;
                v___x_5519_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_5498_,
                    v___x_5518_,
                );
                v___x_5520_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                v___x_5521_ = lean_string_append(v___x_5519_, v___x_5520_);
                v___x_5522_ = l_Lake_Name_eraseHead(v_facet_5489_);
                v___x_5523_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_5522_,
                    v___x_5518_,
                );
                v___x_5524_ = lean_string_append(v___x_5521_, v___x_5523_);
                lean_dec_ref(v___x_5523_);
                v___x_5525_ = 0;
                if v_isShared_5515_ == 0 {
                    lean_ctor_set(v___x_5514_, 2, v___x_5524_);
                    v_job_5527_ = v___x_5514_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_task_5511_);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 1, v_kind_5512_);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 2, v___x_5524_);
                    v_job_5527_ = v_reuseFailAlloc_5535_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_5527_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5525_,
                );
                lean_inc_ref(v_job_5527_);
                v___x_5528_ = l_Lake_Job_toOpaque___redArg(v_job_5527_);
                v___x_5529_ = lean_array_push(v___x_5517_, v___x_5528_);
                v___x_5530_ = lean_st_ref_set(v_registeredJobs_5516_, v___x_5529_);
                v___x_5531_ = l_Lake_Job_renew___redArg(v_job_5527_);
                if v_isShared_5510_ == 0 {
                    lean_ctor_set(v___x_5509_, 0, v___x_5531_);
                    v___x_5533_ = v___x_5509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5534_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5534_, 0, v___x_5531_);
                    lean_ctor_set(v_reuseFailAlloc_5534_, 1, v_a_5507_);
                    v___x_5533_ = v_reuseFailAlloc_5534_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(
    mut v_what_5539_: *mut LeanObject,
    mut v_optFacet_5540_: *mut LeanObject,
    mut v___x_5541_: *mut LeanObject,
    mut v_facet_5542_: *mut LeanObject,
    mut v_pkg_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5551_: *mut LeanObject = core::ptr::null_mut();
    v_res_5551_ =
        l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(
            v_what_5539_,
            v_optFacet_5540_,
            v___x_5541_,
            v_facet_5542_,
            v_pkg_5543_,
            v___y_5544_,
            v___y_5545_,
            v___y_5546_,
            v___y_5547_,
            v___y_5548_,
            v___y_5549_,
        );
    lean_dec_ref(v___y_5548_);
    lean_dec(v___y_5547_);
    lean_dec(v___y_5546_);
    lean_dec(v___y_5545_);
    return v_res_5551_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(
    mut v_facet_5559_: *mut LeanObject,
    mut v_optFacet_5560_: *mut LeanObject,
    mut v_what_5561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: u8 = 0;
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    v___x_5562_ = l_Lake_instDataKindUnit;
    v___f_5563_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed as *mut core::ffi::c_void, 12, 4);
    lean_closure_set(v___f_5563_, 0, v_what_5561_);
    lean_closure_set(v___f_5563_, 1, v_optFacet_5560_);
    lean_closure_set(v___f_5563_, 2, v___x_5562_);
    lean_closure_set(v___f_5563_, 3, v_facet_5559_);
    v___x_5564_ = l_Lake_Package_keyword;
    v___x_5565_ = 1;
    v___x_5566_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3;
    v___x_5567_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_5567_, 0, v___x_5564_);
    lean_ctor_set(v___x_5567_, 1, v___f_5563_);
    lean_ctor_set(v___x_5567_, 2, v___x_5562_);
    lean_ctor_set(v___x_5567_, 3, v___x_5566_);
    lean_ctor_set_uint8(
        v___x_5567_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_5565_,
    );
    lean_ctor_set_uint8(
        v___x_5567_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_5565_,
    );
    return v___x_5567_;
}
pub unsafe fn l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(
    mut v_facet_5568_: *mut LeanObject,
    mut v_optFacet_5569_: *mut LeanObject,
    mut v_what_5570_: *mut LeanObject,
    mut v_inst_5571_: *mut LeanObject,
    mut v_inst_5572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: u8 = 0;
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    v___x_5573_ = l_Lake_instDataKindUnit;
    v___f_5574_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed as *mut core::ffi::c_void, 12, 4);
    lean_closure_set(v___f_5574_, 0, v_what_5570_);
    lean_closure_set(v___f_5574_, 1, v_optFacet_5569_);
    lean_closure_set(v___f_5574_, 2, v___x_5573_);
    lean_closure_set(v___f_5574_, 3, v_facet_5568_);
    v___x_5575_ = l_Lake_Package_keyword;
    v___x_5576_ = 1;
    v___x_5577_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3;
    v___x_5578_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_5578_, 0, v___x_5575_);
    lean_ctor_set(v___x_5578_, 1, v___f_5574_);
    lean_ctor_set(v___x_5578_, 2, v___x_5573_);
    lean_ctor_set(v___x_5578_, 3, v___x_5577_);
    lean_ctor_set_uint8(
        v___x_5578_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_5576_,
    );
    lean_ctor_set_uint8(
        v___x_5578_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_5576_,
    );
    return v___x_5578_;
}
pub unsafe fn l_Lake_Package_buildCacheFacetConfig___lam__1(
    mut v_baseName_5580_: *mut LeanObject,
    mut v___x_5581_: *mut LeanObject,
    mut v_success_5582_: u8,
    mut v___y_5583_: *mut LeanObject,
    mut v___y_5584_: *mut LeanObject,
    mut v___y_5585_: *mut LeanObject,
    mut v___y_5586_: *mut LeanObject,
    mut v___y_5587_: *mut LeanObject,
    mut v___y_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5594_: u8 = 0;
    let mut v_wantsRebuild_5595_: u8 = 0;
    let mut v_trace_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5600_: u8 = 0;
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: u8 = 0;
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5611_: u8 = 0;
    let mut v_toBuildConfig_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_5613_: u8 = 0;
    let mut v___x_5614_: u8 = 0;
    let mut v___x_5615_: u8 = 0;
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_success_5582_ == 0 {
                    v_toBuildConfig_5612_ = lean_ctor_get(v___y_5587_, 0);
                    v_verbosity_5613_ = lean_ctor_get_uint8(
                        v_toBuildConfig_5612_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v___x_5614_ = 2;
                    v___x_5615_ = l_Lake_instDecidableEqVerbosity(v_verbosity_5613_, v___x_5614_);
                    if v___x_5615_ == 0 {
                        lean_dec(v___x_5581_);
                        lean_dec(v_baseName_5580_);
                        v___x_5616_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
                        v_a_5591_ = v___x_5616_;
                        v_a_5592_ = v___y_5588_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5617_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
                        v___x_5618_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_baseName_5580_,
                                v___x_5615_,
                            );
                        v___x_5619_ = lean_string_append(v___x_5617_, v___x_5618_);
                        lean_dec_ref(v___x_5618_);
                        v___x_5620_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                        v___x_5621_ = lean_string_append(v___x_5619_, v___x_5620_);
                        v___x_5622_ = l_Lake_Name_eraseHead(v___x_5581_);
                        v___x_5623_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_5622_,
                                v___x_5615_,
                            );
                        v___x_5624_ = lean_string_append(v___x_5621_, v___x_5623_);
                        lean_dec_ref(v___x_5623_);
                        v___x_5625_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
                        v___x_5626_ = lean_string_append(v___x_5624_, v___x_5625_);
                        v_a_5591_ = v___x_5626_;
                        v_a_5592_ = v___y_5588_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5581_);
                    lean_dec(v_baseName_5580_);
                    v___x_5627_ = lean_box(0);
                    v___x_5628_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5628_, 0, v___x_5627_);
                    lean_ctor_set(v___x_5628_, 1, v___y_5588_);
                    return v___x_5628_;
                }
            }
            1 => {
                v_log_5593_ = lean_ctor_get(v_a_5592_, 0);
                v_action_5594_ = lean_ctor_get_uint8(
                    v_a_5592_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5595_ = lean_ctor_get_uint8(
                    v_a_5592_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_5596_ = lean_ctor_get(v_a_5592_, 1);
                v_buildTime_5597_ = lean_ctor_get(v_a_5592_, 2);
                v_isSharedCheck_5611_ = (!lean_is_exclusive(v_a_5592_)) as u8;
                if v_isSharedCheck_5611_ == 0 {
                    v___x_5599_ = v_a_5592_;
                    v_isShared_5600_ = v_isSharedCheck_5611_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_buildTime_5597_);
                    lean_inc(v_trace_5596_);
                    lean_inc(v_log_5593_);
                    lean_dec(v_a_5592_);
                    v___x_5599_ = lean_box(0);
                    v_isShared_5600_ = v_isSharedCheck_5611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5601_ = l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0;
                v___x_5602_ = lean_string_append(v___x_5601_, v_a_5591_);
                lean_dec_ref(v_a_5591_);
                v___x_5603_ = 3;
                v___x_5604_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5604_, 0, v___x_5602_);
                lean_ctor_set_uint8(
                    v___x_5604_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5603_,
                );
                v___x_5605_ = lean_array_get_size(v_log_5593_);
                v___x_5606_ = lean_array_push(v_log_5593_, v___x_5604_);
                if v_isShared_5600_ == 0 {
                    lean_ctor_set(v___x_5599_, 0, v___x_5606_);
                    v___x_5608_ = v___x_5599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5610_, 0, v___x_5606_);
                    lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_trace_5596_);
                    lean_ctor_set(v_reuseFailAlloc_5610_, 2, v_buildTime_5597_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5610_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5594_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5610_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5595_,
                    );
                    v___x_5608_ = v_reuseFailAlloc_5610_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5609_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5609_, 0, v___x_5605_);
                lean_ctor_set(v___x_5609_, 1, v___x_5608_);
                return v___x_5609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(
    mut v_baseName_5629_: *mut LeanObject,
    mut v___x_5630_: *mut LeanObject,
    mut v_success_5631_: *mut LeanObject,
    mut v___y_5632_: *mut LeanObject,
    mut v___y_5633_: *mut LeanObject,
    mut v___y_5634_: *mut LeanObject,
    mut v___y_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_success_boxed_5639_: u8 = 0;
    let mut v_res_5640_: *mut LeanObject = core::ptr::null_mut();
    v_success_boxed_5639_ = (lean_unbox(v_success_5631_) as u8);
    v_res_5640_ = l_Lake_Package_buildCacheFacetConfig___lam__1(
        v_baseName_5629_,
        v___x_5630_,
        v_success_boxed_5639_,
        v___y_5632_,
        v___y_5633_,
        v___y_5634_,
        v___y_5635_,
        v___y_5636_,
        v___y_5637_,
    );
    lean_dec_ref(v___y_5636_);
    lean_dec(v___y_5635_);
    lean_dec(v___y_5634_);
    lean_dec(v___y_5633_);
    lean_dec_ref(v___y_5632_);
    return v_res_5640_;
}
pub unsafe fn l_Lake_Package_buildCacheFacetConfig___lam__2(
    mut v___x_5641_: *mut LeanObject,
    mut v___x_5642_: *mut LeanObject,
    mut v___x_5643_: *mut LeanObject,
    mut v_pkg_5644_: *mut LeanObject,
    mut v___y_5645_: *mut LeanObject,
    mut v___y_5646_: *mut LeanObject,
    mut v___y_5647_: *mut LeanObject,
    mut v___y_5648_: *mut LeanObject,
    mut v___y_5649_: *mut LeanObject,
    mut v___y_5650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_baseName_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5664_: u8 = 0;
    let mut v_task_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5669_: u8 = 0;
    let mut v_registeredJobs_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: u8 = 0;
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: u8 = 0;
    let mut v_job_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5690_: u8 = 0;
    let mut v_unused_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_baseName_5652_ = lean_ctor_get(v_pkg_5644_, 1);
                lean_inc_n(v_baseName_5652_, 2);
                v_keyName_5653_ = lean_ctor_get(v_pkg_5644_, 2);
                lean_inc(v___x_5641_);
                v___f_5654_ = lean_alloc_closure(
                    l_Lake_Package_buildCacheFacetConfig___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    2,
                );
                lean_closure_set(v___f_5654_, 0, v_baseName_5652_);
                lean_closure_set(v___f_5654_, 1, v___x_5641_);
                lean_inc(v_keyName_5653_);
                v___x_5655_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5655_, 0, v_keyName_5653_);
                v___x_5656_ = l_Lake_Package_keyword;
                v___x_5657_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_5657_, 0, v___x_5655_);
                lean_ctor_set(v___x_5657_, 1, v___x_5656_);
                lean_ctor_set(v___x_5657_, 2, v_pkg_5644_);
                lean_ctor_set(v___x_5657_, 3, v___x_5641_);
                lean_inc(v___x_5642_);
                v___f_5658_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_5658_, 0, v___x_5657_);
                lean_closure_set(v___f_5658_, 1, v___x_5642_);
                lean_closure_set(v___f_5658_, 2, v___f_5654_);
                v___x_5659_ = l_Lake_ensureJob___redArg(
                    v___x_5642_,
                    v___f_5658_,
                    v___y_5645_,
                    v___y_5646_,
                    v___y_5647_,
                    v___y_5648_,
                    v___y_5649_,
                    v___y_5650_,
                );
                if lean_obj_tag(v___x_5659_) == 0 {
                    v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
                    v_a_5661_ = lean_ctor_get(v___x_5659_, 1);
                    v_isSharedCheck_5692_ = (!lean_is_exclusive(v___x_5659_)) as u8;
                    if v_isSharedCheck_5692_ == 0 {
                        v___x_5663_ = v___x_5659_;
                        v_isShared_5664_ = v_isSharedCheck_5692_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5661_);
                        lean_inc(v_a_5660_);
                        lean_dec(v___x_5659_);
                        v___x_5663_ = lean_box(0);
                        v_isShared_5664_ = v_isSharedCheck_5692_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_baseName_5652_);
                    lean_dec(v___x_5643_);
                    return v___x_5659_;
                }
            }
            1 => {
                v_task_5665_ = lean_ctor_get(v_a_5660_, 0);
                v_kind_5666_ = lean_ctor_get(v_a_5660_, 1);
                v_isSharedCheck_5690_ = (!lean_is_exclusive(v_a_5660_)) as u8;
                if v_isSharedCheck_5690_ == 0 {
                    v_unused_5691_ = lean_ctor_get(v_a_5660_, 2);
                    lean_dec(v_unused_5691_);
                    v___x_5668_ = v_a_5660_;
                    v_isShared_5669_ = v_isSharedCheck_5690_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_5666_);
                    lean_inc(v_task_5665_);
                    lean_dec(v_a_5660_);
                    v___x_5668_ = lean_box(0);
                    v_isShared_5669_ = v_isSharedCheck_5690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_5670_ = lean_ctor_get(v___y_5649_, 3);
                v___x_5671_ = lean_st_ref_take(v_registeredJobs_5670_);
                v___x_5672_ = 1;
                v___x_5673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_5652_,
                    v___x_5672_,
                );
                v___x_5674_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                v___x_5675_ = lean_string_append(v___x_5673_, v___x_5674_);
                v___x_5676_ = l_Lake_Name_eraseHead(v___x_5643_);
                v___x_5677_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_5676_,
                    v___x_5672_,
                );
                v___x_5678_ = lean_string_append(v___x_5675_, v___x_5677_);
                lean_dec_ref(v___x_5677_);
                v___x_5679_ = 0;
                if v_isShared_5669_ == 0 {
                    lean_ctor_set(v___x_5668_, 2, v___x_5678_);
                    v_job_5681_ = v___x_5668_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_task_5665_);
                    lean_ctor_set(v_reuseFailAlloc_5689_, 1, v_kind_5666_);
                    lean_ctor_set(v_reuseFailAlloc_5689_, 2, v___x_5678_);
                    v_job_5681_ = v_reuseFailAlloc_5689_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_5681_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5679_,
                );
                lean_inc_ref(v_job_5681_);
                v___x_5682_ = l_Lake_Job_toOpaque___redArg(v_job_5681_);
                v___x_5683_ = lean_array_push(v___x_5671_, v___x_5682_);
                v___x_5684_ = lean_st_ref_set(v_registeredJobs_5670_, v___x_5683_);
                v___x_5685_ = l_Lake_Job_renew___redArg(v_job_5681_);
                if v_isShared_5664_ == 0 {
                    lean_ctor_set(v___x_5663_, 0, v___x_5685_);
                    v___x_5687_ = v___x_5663_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5688_, 0, v___x_5685_);
                    lean_ctor_set(v_reuseFailAlloc_5688_, 1, v_a_5661_);
                    v___x_5687_ = v_reuseFailAlloc_5688_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(
    mut v___x_5693_: *mut LeanObject,
    mut v___x_5694_: *mut LeanObject,
    mut v___x_5695_: *mut LeanObject,
    mut v_pkg_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
    mut v___y_5703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5704_: *mut LeanObject = core::ptr::null_mut();
    v_res_5704_ = l_Lake_Package_buildCacheFacetConfig___lam__2(
        v___x_5693_,
        v___x_5694_,
        v___x_5695_,
        v_pkg_5696_,
        v___y_5697_,
        v___y_5698_,
        v___y_5699_,
        v___y_5700_,
        v___y_5701_,
        v___y_5702_,
    );
    lean_dec_ref(v___y_5701_);
    lean_dec(v___y_5700_);
    lean_dec(v___y_5699_);
    lean_dec(v___y_5698_);
    return v_res_5704_;
}
pub unsafe fn _init_l_Lake_Package_buildCacheFacetConfig___closed__0() -> *mut LeanObject {
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5708_: *mut LeanObject = core::ptr::null_mut();
    v___x_5705_ = l_Lake_Package_buildCacheFacet;
    v___x_5706_ = l_Lake_instDataKindUnit;
    v___x_5707_ = l_Lake_Package_optBuildCacheFacet;
    v___f_5708_ = lean_alloc_closure(
        l_Lake_Package_buildCacheFacetConfig___lam__2___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    lean_closure_set(v___f_5708_, 0, v___x_5707_);
    lean_closure_set(v___f_5708_, 1, v___x_5706_);
    lean_closure_set(v___f_5708_, 2, v___x_5705_);
    return v___f_5708_;
}
pub unsafe fn _init_l_Lake_Package_buildCacheFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___f_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: u8 = 0;
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    v___f_5709_ = l_Lake_Package_extraDepFacetConfig___closed__0;
    v___x_5710_ = 1;
    v___x_5711_ = l_Lake_instDataKindUnit;
    v___f_5712_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_buildCacheFacetConfig___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Package_buildCacheFacetConfig___closed__0_once),
        _init_l_Lake_Package_buildCacheFacetConfig___closed__0,
    );
    v___x_5713_ = l_Lake_Package_keyword;
    v___x_5714_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_5714_, 0, v___x_5713_);
    lean_ctor_set(v___x_5714_, 1, v___f_5712_);
    lean_ctor_set(v___x_5714_, 2, v___x_5711_);
    lean_ctor_set(v___x_5714_, 3, v___f_5709_);
    lean_ctor_set_uint8(
        v___x_5714_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_5710_,
    );
    lean_ctor_set_uint8(
        v___x_5714_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_5710_,
    );
    return v___x_5714_;
}
pub unsafe fn _init_l_Lake_Package_buildCacheFacetConfig() -> *mut LeanObject {
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    v___x_5715_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_buildCacheFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Package_buildCacheFacetConfig___closed__1_once),
        _init_l_Lake_Package_buildCacheFacetConfig___closed__1,
    );
    return v___x_5715_;
}
pub unsafe fn l_Lake_Package_optBarrelFacetConfig___lam__0(
    mut v_pkg_5717_: *mut LeanObject,
    mut v___x_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_5727_: u8 = 0;
    let mut v___y_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5734_: u8 = 0;
    let mut v_wantsRebuild_5735_: u8 = 0;
    let mut v_trace_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v___x_5741_: u8 = 0;
    let mut v___x_5742_: u8 = 0;
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: u8 = 0;
    let mut v_reuseFailAlloc_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5747_: u8 = 0;
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: u8 = 0;
    let mut v_a_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_pkg_5717_);
                v___x_5748_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(
                    v_pkg_5717_,
                    v___y_5723_,
                    v___y_5724_,
                );
                if lean_obj_tag(v___x_5748_) == 0 {
                    v_a_5749_ = lean_ctor_get(v___x_5748_, 0);
                    lean_inc(v_a_5749_);
                    v_a_5750_ = lean_ctor_get(v___x_5748_, 1);
                    lean_inc(v_a_5750_);
                    lean_dec_ref_known(v___x_5748_, 2);
                    v_dir_5751_ = lean_ctor_get(v_pkg_5717_, 4);
                    v___x_5752_ = l_Lake_defaultLakeDir;
                    lean_inc_ref(v_dir_5751_);
                    v___x_5753_ = l_Lake_joinRelative(v_dir_5751_, v___x_5752_);
                    v___x_5754_ = l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0;
                    v___x_5755_ = l_Lake_joinRelative(v___x_5753_, v___x_5754_);
                    v___x_5756_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(
                        v_pkg_5717_,
                        v_a_5749_,
                        v___x_5755_,
                        v___x_5718_,
                        v___y_5719_,
                        v___y_5720_,
                        v___y_5721_,
                        v___y_5722_,
                        v___y_5723_,
                        v_a_5750_,
                    );
                    if lean_obj_tag(v___x_5756_) == 0 {
                        v_a_5757_ = lean_ctor_get(v___x_5756_, 1);
                        lean_inc(v_a_5757_);
                        lean_dec_ref_known(v___x_5756_, 2);
                        v___x_5758_ = 1;
                        v_r_5727_ = v___x_5758_;
                        v___y_5728_ = v_a_5757_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5759_ = lean_ctor_get(v___x_5756_, 1);
                        lean_inc(v_a_5759_);
                        lean_dec_ref_known(v___x_5756_, 2);
                        v_a_5732_ = v_a_5759_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pkg_5717_);
                    v_a_5760_ = lean_ctor_get(v___x_5748_, 1);
                    lean_inc(v_a_5760_);
                    lean_dec_ref_known(v___x_5748_, 2);
                    v_a_5732_ = v_a_5760_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5729_ = lean_box((v_r_5727_) as usize);
                v___x_5730_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5730_, 0, v___x_5729_);
                lean_ctor_set(v___x_5730_, 1, v___y_5728_);
                return v___x_5730_;
            }
            2 => {
                v_log_5733_ = lean_ctor_get(v_a_5732_, 0);
                v_action_5734_ = lean_ctor_get_uint8(
                    v_a_5732_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5735_ = lean_ctor_get_uint8(
                    v_a_5732_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_5736_ = lean_ctor_get(v_a_5732_, 1);
                v_buildTime_5737_ = lean_ctor_get(v_a_5732_, 2);
                v_isSharedCheck_5747_ = (!lean_is_exclusive(v_a_5732_)) as u8;
                if v_isSharedCheck_5747_ == 0 {
                    v___x_5739_ = v_a_5732_;
                    v_isShared_5740_ = v_isSharedCheck_5747_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_buildTime_5737_);
                    lean_inc(v_trace_5736_);
                    lean_inc(v_log_5733_);
                    lean_dec(v_a_5732_);
                    v___x_5739_ = lean_box(0);
                    v_isShared_5740_ = v_isSharedCheck_5747_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5741_ = 4;
                v___x_5742_ = l_Lake_JobAction_merge(v_action_5734_, v___x_5741_);
                if v_isShared_5740_ == 0 {
                    v___x_5744_ = v___x_5739_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_log_5733_);
                    lean_ctor_set(v_reuseFailAlloc_5746_, 1, v_trace_5736_);
                    lean_ctor_set(v_reuseFailAlloc_5746_, 2, v_buildTime_5737_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5746_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5735_,
                    );
                    v___x_5744_ = v_reuseFailAlloc_5746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_5744_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5742_,
                );
                v___x_5745_ = 0;
                v_r_5727_ = v___x_5745_;
                v___y_5728_ = v___x_5744_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(
    mut v_pkg_5761_: *mut LeanObject,
    mut v___x_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5770_: *mut LeanObject = core::ptr::null_mut();
    v_res_5770_ = l_Lake_Package_optBarrelFacetConfig___lam__0(
        v_pkg_5761_,
        v___x_5762_,
        v___y_5763_,
        v___y_5764_,
        v___y_5765_,
        v___y_5766_,
        v___y_5767_,
        v___y_5768_,
    );
    lean_dec_ref(v___y_5767_);
    lean_dec(v___y_5766_);
    lean_dec(v___y_5765_);
    lean_dec(v___y_5764_);
    lean_dec_ref(v___y_5763_);
    lean_dec_ref(v___x_5762_);
    return v_res_5770_;
}
pub unsafe fn l_Lake_Package_optBarrelFacetConfig___lam__1(
    mut v___x_5771_: *mut LeanObject,
    mut v___f_5772_: *mut LeanObject,
    mut v___x_5773_: *mut LeanObject,
    mut v___x_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
    mut v___y_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    v___x_5782_ = l_Lake_Job_async___redArg(
        v___x_5771_,
        v___f_5772_,
        v___x_5773_,
        v___x_5774_,
        v___y_5775_,
        v___y_5776_,
        v___y_5777_,
        v___y_5778_,
        v___y_5779_,
    );
    v___x_5783_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5783_, 0, v___x_5782_);
    lean_ctor_set(v___x_5783_, 1, v___y_5780_);
    return v___x_5783_;
}
pub unsafe fn l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(
    mut v___x_5784_: *mut LeanObject,
    mut v___f_5785_: *mut LeanObject,
    mut v___x_5786_: *mut LeanObject,
    mut v___x_5787_: *mut LeanObject,
    mut v___y_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5795_: *mut LeanObject = core::ptr::null_mut();
    v_res_5795_ = l_Lake_Package_optBarrelFacetConfig___lam__1(
        v___x_5784_,
        v___f_5785_,
        v___x_5786_,
        v___x_5787_,
        v___y_5788_,
        v___y_5789_,
        v___y_5790_,
        v___y_5791_,
        v___y_5792_,
        v___y_5793_,
    );
    lean_dec_ref(v___y_5792_);
    lean_dec(v___y_5791_);
    lean_dec(v___y_5790_);
    lean_dec(v___y_5789_);
    return v_res_5795_;
}
pub unsafe fn l_Lake_Package_optBarrelFacetConfig___lam__2(
    mut v___x_5796_: *mut LeanObject,
    mut v___x_5797_: *mut LeanObject,
    mut v___x_5798_: *mut LeanObject,
    mut v_pkg_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
    mut v___y_5805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5816_: u8 = 0;
    let mut v_task_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5821_: u8 = 0;
    let mut v_registeredJobs_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: u8 = 0;
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5842_: u8 = 0;
    let mut v_unused_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_pkg_5799_);
                v___f_5807_ = lean_alloc_closure(
                    l_Lake_Package_optBarrelFacetConfig___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                lean_closure_set(v___f_5807_, 0, v_pkg_5799_);
                lean_closure_set(v___f_5807_, 1, v___x_5796_);
                v___x_5808_ = lean_unsigned_to_nat(0);
                v___x_5809_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                lean_inc(v___x_5797_);
                v___f_5810_ = lean_alloc_closure(
                    l_Lake_Package_optBarrelFacetConfig___lam__1___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___f_5810_, 0, v___x_5797_);
                lean_closure_set(v___f_5810_, 1, v___f_5807_);
                lean_closure_set(v___f_5810_, 2, v___x_5808_);
                lean_closure_set(v___f_5810_, 3, v___x_5809_);
                v___x_5811_ = l_Lake_ensureJob___redArg(
                    v___x_5797_,
                    v___f_5810_,
                    v___y_5800_,
                    v___y_5801_,
                    v___y_5802_,
                    v___y_5803_,
                    v___y_5804_,
                    v___y_5805_,
                );
                if lean_obj_tag(v___x_5811_) == 0 {
                    v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
                    v_a_5813_ = lean_ctor_get(v___x_5811_, 1);
                    v_isSharedCheck_5844_ = (!lean_is_exclusive(v___x_5811_)) as u8;
                    if v_isSharedCheck_5844_ == 0 {
                        v___x_5815_ = v___x_5811_;
                        v_isShared_5816_ = v_isSharedCheck_5844_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5813_);
                        lean_inc(v_a_5812_);
                        lean_dec(v___x_5811_);
                        v___x_5815_ = lean_box(0);
                        v_isShared_5816_ = v_isSharedCheck_5844_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pkg_5799_);
                    lean_dec(v___x_5798_);
                    return v___x_5811_;
                }
            }
            1 => {
                v_task_5817_ = lean_ctor_get(v_a_5812_, 0);
                v_kind_5818_ = lean_ctor_get(v_a_5812_, 1);
                v_isSharedCheck_5842_ = (!lean_is_exclusive(v_a_5812_)) as u8;
                if v_isSharedCheck_5842_ == 0 {
                    v_unused_5843_ = lean_ctor_get(v_a_5812_, 2);
                    lean_dec(v_unused_5843_);
                    v___x_5820_ = v_a_5812_;
                    v_isShared_5821_ = v_isSharedCheck_5842_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_5818_);
                    lean_inc(v_task_5817_);
                    lean_dec(v_a_5812_);
                    v___x_5820_ = lean_box(0);
                    v_isShared_5821_ = v_isSharedCheck_5842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_5822_ = lean_ctor_get(v___y_5804_, 3);
                v___x_5823_ = lean_st_ref_take(v_registeredJobs_5822_);
                v_baseName_5824_ = lean_ctor_get(v_pkg_5799_, 1);
                lean_inc(v_baseName_5824_);
                lean_dec_ref(v_pkg_5799_);
                v___x_5825_ = 1;
                v___x_5826_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_5824_,
                    v___x_5825_,
                );
                v___x_5827_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                v___x_5828_ = lean_string_append(v___x_5826_, v___x_5827_);
                v___x_5829_ = l_Lake_Name_eraseHead(v___x_5798_);
                v___x_5830_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_5829_,
                    v___x_5825_,
                );
                v___x_5831_ = lean_string_append(v___x_5828_, v___x_5830_);
                lean_dec_ref(v___x_5830_);
                if v_isShared_5821_ == 0 {
                    lean_ctor_set(v___x_5820_, 2, v___x_5831_);
                    v_job_5833_ = v___x_5820_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5841_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_task_5817_);
                    lean_ctor_set(v_reuseFailAlloc_5841_, 1, v_kind_5818_);
                    lean_ctor_set(v_reuseFailAlloc_5841_, 2, v___x_5831_);
                    v_job_5833_ = v_reuseFailAlloc_5841_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_5833_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5825_,
                );
                lean_inc_ref(v_job_5833_);
                v___x_5834_ = l_Lake_Job_toOpaque___redArg(v_job_5833_);
                v___x_5835_ = lean_array_push(v___x_5823_, v___x_5834_);
                v___x_5836_ = lean_st_ref_set(v_registeredJobs_5822_, v___x_5835_);
                v___x_5837_ = l_Lake_Job_renew___redArg(v_job_5833_);
                if v_isShared_5816_ == 0 {
                    lean_ctor_set(v___x_5815_, 0, v___x_5837_);
                    v___x_5839_ = v___x_5815_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5840_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5840_, 0, v___x_5837_);
                    lean_ctor_set(v_reuseFailAlloc_5840_, 1, v_a_5813_);
                    v___x_5839_ = v_reuseFailAlloc_5840_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(
    mut v___x_5845_: *mut LeanObject,
    mut v___x_5846_: *mut LeanObject,
    mut v___x_5847_: *mut LeanObject,
    mut v_pkg_5848_: *mut LeanObject,
    mut v___y_5849_: *mut LeanObject,
    mut v___y_5850_: *mut LeanObject,
    mut v___y_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
    mut v___y_5855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5856_: *mut LeanObject = core::ptr::null_mut();
    v_res_5856_ = l_Lake_Package_optBarrelFacetConfig___lam__2(
        v___x_5845_,
        v___x_5846_,
        v___x_5847_,
        v_pkg_5848_,
        v___y_5849_,
        v___y_5850_,
        v___y_5851_,
        v___y_5852_,
        v___y_5853_,
        v___y_5854_,
    );
    lean_dec_ref(v___y_5853_);
    lean_dec(v___y_5852_);
    lean_dec(v___y_5851_);
    lean_dec(v___y_5850_);
    return v_res_5856_;
}
pub unsafe fn _init_l_Lake_Package_optBarrelFacetConfig___closed__0() -> *mut LeanObject {
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5860_: *mut LeanObject = core::ptr::null_mut();
    v___x_5857_ = l_Lake_Package_optReservoirBarrelFacet;
    v___x_5858_ = l_Lake_instDataKindBool;
    v___x_5859_ = l_Lake_Reservoir_lakeHeaders;
    v___f_5860_ = lean_alloc_closure(
        l_Lake_Package_optBarrelFacetConfig___lam__2___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    lean_closure_set(v___f_5860_, 0, v___x_5859_);
    lean_closure_set(v___f_5860_, 1, v___x_5858_);
    lean_closure_set(v___f_5860_, 2, v___x_5857_);
    return v___f_5860_;
}
pub unsafe fn _init_l_Lake_Package_optBarrelFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___f_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: u8 = 0;
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    v___f_5861_ = l_Lake_Package_optBuildCacheFacetConfig___closed__1;
    v___x_5862_ = 1;
    v___x_5863_ = l_Lake_instDataKindBool;
    v___f_5864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_optBarrelFacetConfig___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Package_optBarrelFacetConfig___closed__0_once),
        _init_l_Lake_Package_optBarrelFacetConfig___closed__0,
    );
    v___x_5865_ = l_Lake_Package_keyword;
    v___x_5866_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_5866_, 0, v___x_5865_);
    lean_ctor_set(v___x_5866_, 1, v___f_5864_);
    lean_ctor_set(v___x_5866_, 2, v___x_5863_);
    lean_ctor_set(v___x_5866_, 3, v___f_5861_);
    lean_ctor_set_uint8(
        v___x_5866_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_5862_,
    );
    lean_ctor_set_uint8(
        v___x_5866_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_5862_,
    );
    return v___x_5866_;
}
pub unsafe fn _init_l_Lake_Package_optBarrelFacetConfig() -> *mut LeanObject {
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    v___x_5867_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_optBarrelFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Package_optBarrelFacetConfig___closed__1_once),
        _init_l_Lake_Package_optBarrelFacetConfig___closed__1,
    );
    return v___x_5867_;
}
pub unsafe fn l_Lake_Package_barrelFacetConfig___lam__1(
    mut v_baseName_5869_: *mut LeanObject,
    mut v___x_5870_: *mut LeanObject,
    mut v_success_5871_: u8,
    mut v___y_5872_: *mut LeanObject,
    mut v___y_5873_: *mut LeanObject,
    mut v___y_5874_: *mut LeanObject,
    mut v___y_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
    mut v___y_5877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_5883_: u8 = 0;
    let mut v_wantsRebuild_5884_: u8 = 0;
    let mut v_trace_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5889_: u8 = 0;
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: u8 = 0;
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5900_: u8 = 0;
    let mut v_toBuildConfig_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_5902_: u8 = 0;
    let mut v___x_5903_: u8 = 0;
    let mut v___x_5904_: u8 = 0;
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_success_5871_ == 0 {
                    v_toBuildConfig_5901_ = lean_ctor_get(v___y_5876_, 0);
                    v_verbosity_5902_ = lean_ctor_get_uint8(
                        v_toBuildConfig_5901_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v___x_5903_ = 2;
                    v___x_5904_ = l_Lake_instDecidableEqVerbosity(v_verbosity_5902_, v___x_5903_);
                    if v___x_5904_ == 0 {
                        lean_dec(v___x_5870_);
                        lean_dec(v_baseName_5869_);
                        v___x_5905_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
                        v_a_5880_ = v___x_5905_;
                        v_a_5881_ = v___y_5877_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5906_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
                        v___x_5907_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_baseName_5869_,
                                v___x_5904_,
                            );
                        v___x_5908_ = lean_string_append(v___x_5906_, v___x_5907_);
                        lean_dec_ref(v___x_5907_);
                        v___x_5909_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                        v___x_5910_ = lean_string_append(v___x_5908_, v___x_5909_);
                        v___x_5911_ = l_Lake_Name_eraseHead(v___x_5870_);
                        v___x_5912_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_5911_,
                                v___x_5904_,
                            );
                        v___x_5913_ = lean_string_append(v___x_5910_, v___x_5912_);
                        lean_dec_ref(v___x_5912_);
                        v___x_5914_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
                        v___x_5915_ = lean_string_append(v___x_5913_, v___x_5914_);
                        v_a_5880_ = v___x_5915_;
                        v_a_5881_ = v___y_5877_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5870_);
                    lean_dec(v_baseName_5869_);
                    v___x_5916_ = lean_box(0);
                    v___x_5917_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5917_, 0, v___x_5916_);
                    lean_ctor_set(v___x_5917_, 1, v___y_5877_);
                    return v___x_5917_;
                }
            }
            1 => {
                v_log_5882_ = lean_ctor_get(v_a_5881_, 0);
                v_action_5883_ = lean_ctor_get_uint8(
                    v_a_5881_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5884_ = lean_ctor_get_uint8(
                    v_a_5881_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_5885_ = lean_ctor_get(v_a_5881_, 1);
                v_buildTime_5886_ = lean_ctor_get(v_a_5881_, 2);
                v_isSharedCheck_5900_ = (!lean_is_exclusive(v_a_5881_)) as u8;
                if v_isSharedCheck_5900_ == 0 {
                    v___x_5888_ = v_a_5881_;
                    v_isShared_5889_ = v_isSharedCheck_5900_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_buildTime_5886_);
                    lean_inc(v_trace_5885_);
                    lean_inc(v_log_5882_);
                    lean_dec(v_a_5881_);
                    v___x_5888_ = lean_box(0);
                    v_isShared_5889_ = v_isSharedCheck_5900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5890_ = l_Lake_Package_barrelFacetConfig___lam__1___closed__0;
                v___x_5891_ = lean_string_append(v___x_5890_, v_a_5880_);
                lean_dec_ref(v_a_5880_);
                v___x_5892_ = 3;
                v___x_5893_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5893_, 0, v___x_5891_);
                lean_ctor_set_uint8(
                    v___x_5893_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5892_,
                );
                v___x_5894_ = lean_array_get_size(v_log_5882_);
                v___x_5895_ = lean_array_push(v_log_5882_, v___x_5893_);
                if v_isShared_5889_ == 0 {
                    lean_ctor_set(v___x_5888_, 0, v___x_5895_);
                    v___x_5897_ = v___x_5888_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5899_, 0, v___x_5895_);
                    lean_ctor_set(v_reuseFailAlloc_5899_, 1, v_trace_5885_);
                    lean_ctor_set(v_reuseFailAlloc_5899_, 2, v_buildTime_5886_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5899_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_5883_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5899_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5884_,
                    );
                    v___x_5897_ = v_reuseFailAlloc_5899_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5898_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5898_, 0, v___x_5894_);
                lean_ctor_set(v___x_5898_, 1, v___x_5897_);
                return v___x_5898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_barrelFacetConfig___lam__1___boxed(
    mut v_baseName_5918_: *mut LeanObject,
    mut v___x_5919_: *mut LeanObject,
    mut v_success_5920_: *mut LeanObject,
    mut v___y_5921_: *mut LeanObject,
    mut v___y_5922_: *mut LeanObject,
    mut v___y_5923_: *mut LeanObject,
    mut v___y_5924_: *mut LeanObject,
    mut v___y_5925_: *mut LeanObject,
    mut v___y_5926_: *mut LeanObject,
    mut v___y_5927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_success_boxed_5928_: u8 = 0;
    let mut v_res_5929_: *mut LeanObject = core::ptr::null_mut();
    v_success_boxed_5928_ = (lean_unbox(v_success_5920_) as u8);
    v_res_5929_ = l_Lake_Package_barrelFacetConfig___lam__1(
        v_baseName_5918_,
        v___x_5919_,
        v_success_boxed_5928_,
        v___y_5921_,
        v___y_5922_,
        v___y_5923_,
        v___y_5924_,
        v___y_5925_,
        v___y_5926_,
    );
    lean_dec_ref(v___y_5925_);
    lean_dec(v___y_5924_);
    lean_dec(v___y_5923_);
    lean_dec(v___y_5922_);
    lean_dec_ref(v___y_5921_);
    return v_res_5929_;
}
pub unsafe fn l_Lake_Package_barrelFacetConfig___lam__2(
    mut v___x_5930_: *mut LeanObject,
    mut v___x_5931_: *mut LeanObject,
    mut v___x_5932_: *mut LeanObject,
    mut v_pkg_5933_: *mut LeanObject,
    mut v___y_5934_: *mut LeanObject,
    mut v___y_5935_: *mut LeanObject,
    mut v___y_5936_: *mut LeanObject,
    mut v___y_5937_: *mut LeanObject,
    mut v___y_5938_: *mut LeanObject,
    mut v___y_5939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_baseName_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5953_: u8 = 0;
    let mut v_task_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5958_: u8 = 0;
    let mut v_registeredJobs_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: u8 = 0;
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: u8 = 0;
    let mut v_job_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5979_: u8 = 0;
    let mut v_unused_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_baseName_5941_ = lean_ctor_get(v_pkg_5933_, 1);
                lean_inc_n(v_baseName_5941_, 2);
                v_keyName_5942_ = lean_ctor_get(v_pkg_5933_, 2);
                lean_inc(v___x_5930_);
                v___f_5943_ = lean_alloc_closure(
                    l_Lake_Package_barrelFacetConfig___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    2,
                );
                lean_closure_set(v___f_5943_, 0, v_baseName_5941_);
                lean_closure_set(v___f_5943_, 1, v___x_5930_);
                lean_inc(v_keyName_5942_);
                v___x_5944_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5944_, 0, v_keyName_5942_);
                v___x_5945_ = l_Lake_Package_keyword;
                v___x_5946_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_5946_, 0, v___x_5944_);
                lean_ctor_set(v___x_5946_, 1, v___x_5945_);
                lean_ctor_set(v___x_5946_, 2, v_pkg_5933_);
                lean_ctor_set(v___x_5946_, 3, v___x_5930_);
                lean_inc(v___x_5931_);
                v___f_5947_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_5947_, 0, v___x_5946_);
                lean_closure_set(v___f_5947_, 1, v___x_5931_);
                lean_closure_set(v___f_5947_, 2, v___f_5943_);
                v___x_5948_ = l_Lake_ensureJob___redArg(
                    v___x_5931_,
                    v___f_5947_,
                    v___y_5934_,
                    v___y_5935_,
                    v___y_5936_,
                    v___y_5937_,
                    v___y_5938_,
                    v___y_5939_,
                );
                if lean_obj_tag(v___x_5948_) == 0 {
                    v_a_5949_ = lean_ctor_get(v___x_5948_, 0);
                    v_a_5950_ = lean_ctor_get(v___x_5948_, 1);
                    v_isSharedCheck_5981_ = (!lean_is_exclusive(v___x_5948_)) as u8;
                    if v_isSharedCheck_5981_ == 0 {
                        v___x_5952_ = v___x_5948_;
                        v_isShared_5953_ = v_isSharedCheck_5981_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5950_);
                        lean_inc(v_a_5949_);
                        lean_dec(v___x_5948_);
                        v___x_5952_ = lean_box(0);
                        v_isShared_5953_ = v_isSharedCheck_5981_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_baseName_5941_);
                    lean_dec(v___x_5932_);
                    return v___x_5948_;
                }
            }
            1 => {
                v_task_5954_ = lean_ctor_get(v_a_5949_, 0);
                v_kind_5955_ = lean_ctor_get(v_a_5949_, 1);
                v_isSharedCheck_5979_ = (!lean_is_exclusive(v_a_5949_)) as u8;
                if v_isSharedCheck_5979_ == 0 {
                    v_unused_5980_ = lean_ctor_get(v_a_5949_, 2);
                    lean_dec(v_unused_5980_);
                    v___x_5957_ = v_a_5949_;
                    v_isShared_5958_ = v_isSharedCheck_5979_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_5955_);
                    lean_inc(v_task_5954_);
                    lean_dec(v_a_5949_);
                    v___x_5957_ = lean_box(0);
                    v_isShared_5958_ = v_isSharedCheck_5979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_5959_ = lean_ctor_get(v___y_5938_, 3);
                v___x_5960_ = lean_st_ref_take(v_registeredJobs_5959_);
                v___x_5961_ = 1;
                v___x_5962_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_5941_,
                    v___x_5961_,
                );
                v___x_5963_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                v___x_5964_ = lean_string_append(v___x_5962_, v___x_5963_);
                v___x_5965_ = l_Lake_Name_eraseHead(v___x_5932_);
                v___x_5966_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_5965_,
                    v___x_5961_,
                );
                v___x_5967_ = lean_string_append(v___x_5964_, v___x_5966_);
                lean_dec_ref(v___x_5966_);
                v___x_5968_ = 0;
                if v_isShared_5958_ == 0 {
                    lean_ctor_set(v___x_5957_, 2, v___x_5967_);
                    v_job_5970_ = v___x_5957_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5978_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_task_5954_);
                    lean_ctor_set(v_reuseFailAlloc_5978_, 1, v_kind_5955_);
                    lean_ctor_set(v_reuseFailAlloc_5978_, 2, v___x_5967_);
                    v_job_5970_ = v_reuseFailAlloc_5978_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_5970_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_5968_,
                );
                lean_inc_ref(v_job_5970_);
                v___x_5971_ = l_Lake_Job_toOpaque___redArg(v_job_5970_);
                v___x_5972_ = lean_array_push(v___x_5960_, v___x_5971_);
                v___x_5973_ = lean_st_ref_set(v_registeredJobs_5959_, v___x_5972_);
                v___x_5974_ = l_Lake_Job_renew___redArg(v_job_5970_);
                if v_isShared_5953_ == 0 {
                    lean_ctor_set(v___x_5952_, 0, v___x_5974_);
                    v___x_5976_ = v___x_5952_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 0, v___x_5974_);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 1, v_a_5950_);
                    v___x_5976_ = v_reuseFailAlloc_5977_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_barrelFacetConfig___lam__2___boxed(
    mut v___x_5982_: *mut LeanObject,
    mut v___x_5983_: *mut LeanObject,
    mut v___x_5984_: *mut LeanObject,
    mut v_pkg_5985_: *mut LeanObject,
    mut v___y_5986_: *mut LeanObject,
    mut v___y_5987_: *mut LeanObject,
    mut v___y_5988_: *mut LeanObject,
    mut v___y_5989_: *mut LeanObject,
    mut v___y_5990_: *mut LeanObject,
    mut v___y_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5993_: *mut LeanObject = core::ptr::null_mut();
    v_res_5993_ = l_Lake_Package_barrelFacetConfig___lam__2(
        v___x_5982_,
        v___x_5983_,
        v___x_5984_,
        v_pkg_5985_,
        v___y_5986_,
        v___y_5987_,
        v___y_5988_,
        v___y_5989_,
        v___y_5990_,
        v___y_5991_,
    );
    lean_dec_ref(v___y_5990_);
    lean_dec(v___y_5989_);
    lean_dec(v___y_5988_);
    lean_dec(v___y_5987_);
    return v_res_5993_;
}
pub unsafe fn _init_l_Lake_Package_barrelFacetConfig___closed__0() -> *mut LeanObject {
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5997_: *mut LeanObject = core::ptr::null_mut();
    v___x_5994_ = l_Lake_Package_reservoirBarrelFacet;
    v___x_5995_ = l_Lake_instDataKindUnit;
    v___x_5996_ = l_Lake_Package_optReservoirBarrelFacet;
    v___f_5997_ = lean_alloc_closure(
        l_Lake_Package_barrelFacetConfig___lam__2___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    lean_closure_set(v___f_5997_, 0, v___x_5996_);
    lean_closure_set(v___f_5997_, 1, v___x_5995_);
    lean_closure_set(v___f_5997_, 2, v___x_5994_);
    return v___f_5997_;
}
pub unsafe fn _init_l_Lake_Package_barrelFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___f_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: u8 = 0;
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    v___f_5998_ = l_Lake_Package_extraDepFacetConfig___closed__0;
    v___x_5999_ = 1;
    v___x_6000_ = l_Lake_instDataKindUnit;
    v___f_6001_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_barrelFacetConfig___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Package_barrelFacetConfig___closed__0_once),
        _init_l_Lake_Package_barrelFacetConfig___closed__0,
    );
    v___x_6002_ = l_Lake_Package_keyword;
    v___x_6003_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_6003_, 0, v___x_6002_);
    lean_ctor_set(v___x_6003_, 1, v___f_6001_);
    lean_ctor_set(v___x_6003_, 2, v___x_6000_);
    lean_ctor_set(v___x_6003_, 3, v___f_5998_);
    lean_ctor_set_uint8(
        v___x_6003_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_5999_,
    );
    lean_ctor_set_uint8(
        v___x_6003_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_5999_,
    );
    return v___x_6003_;
}
pub unsafe fn _init_l_Lake_Package_barrelFacetConfig() -> *mut LeanObject {
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    v___x_6004_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_barrelFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Package_barrelFacetConfig___closed__1_once),
        _init_l_Lake_Package_barrelFacetConfig___closed__1,
    );
    return v___x_6004_;
}
pub unsafe fn l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(
    mut v_pkg_6005_: *mut LeanObject,
    mut v___x_6006_: *mut LeanObject,
    mut v___y_6007_: *mut LeanObject,
    mut v___y_6008_: *mut LeanObject,
    mut v___y_6009_: *mut LeanObject,
    mut v___y_6010_: *mut LeanObject,
    mut v___y_6011_: *mut LeanObject,
    mut v___y_6012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_6015_: u8 = 0;
    let mut v___y_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_6022_: u8 = 0;
    let mut v_wantsRebuild_6023_: u8 = 0;
    let mut v_trace_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6028_: u8 = 0;
    let mut v___x_6029_: u8 = 0;
    let mut v___x_6030_: u8 = 0;
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: u8 = 0;
    let mut v_reuseFailAlloc_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6035_: u8 = 0;
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildArchive_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: u8 = 0;
    let mut v_a_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_pkg_6005_);
                v___x_6036_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(
                    v_pkg_6005_,
                    v___y_6012_,
                );
                if lean_obj_tag(v___x_6036_) == 0 {
                    v_a_6037_ = lean_ctor_get(v___x_6036_, 0);
                    lean_inc(v_a_6037_);
                    v_a_6038_ = lean_ctor_get(v___x_6036_, 1);
                    lean_inc(v_a_6038_);
                    lean_dec_ref_known(v___x_6036_, 2);
                    v_dir_6039_ = lean_ctor_get(v_pkg_6005_, 4);
                    v_buildArchive_6040_ = lean_ctor_get(v_pkg_6005_, 20);
                    v___x_6041_ = l_Lake_defaultLakeDir;
                    lean_inc_ref(v_dir_6039_);
                    v___x_6042_ = l_Lake_joinRelative(v_dir_6039_, v___x_6041_);
                    lean_inc_ref(v_buildArchive_6040_);
                    v___x_6043_ = l_Lake_joinRelative(v___x_6042_, v_buildArchive_6040_);
                    v___x_6044_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(
                        v_pkg_6005_,
                        v_a_6037_,
                        v___x_6043_,
                        v___x_6006_,
                        v___y_6007_,
                        v___y_6008_,
                        v___y_6009_,
                        v___y_6010_,
                        v___y_6011_,
                        v_a_6038_,
                    );
                    if lean_obj_tag(v___x_6044_) == 0 {
                        v_a_6045_ = lean_ctor_get(v___x_6044_, 1);
                        lean_inc(v_a_6045_);
                        lean_dec_ref_known(v___x_6044_, 2);
                        v___x_6046_ = 1;
                        v_r_6015_ = v___x_6046_;
                        v___y_6016_ = v_a_6045_;
                        state = 1;
                        continue;
                    } else {
                        v_a_6047_ = lean_ctor_get(v___x_6044_, 1);
                        lean_inc(v_a_6047_);
                        lean_dec_ref_known(v___x_6044_, 2);
                        v_a_6020_ = v_a_6047_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pkg_6005_);
                    v_a_6048_ = lean_ctor_get(v___x_6036_, 1);
                    lean_inc(v_a_6048_);
                    lean_dec_ref_known(v___x_6036_, 2);
                    v_a_6020_ = v_a_6048_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6017_ = lean_box((v_r_6015_) as usize);
                v___x_6018_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6018_, 0, v___x_6017_);
                lean_ctor_set(v___x_6018_, 1, v___y_6016_);
                return v___x_6018_;
            }
            2 => {
                v_log_6021_ = lean_ctor_get(v_a_6020_, 0);
                v_action_6022_ = lean_ctor_get_uint8(
                    v_a_6020_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_6023_ = lean_ctor_get_uint8(
                    v_a_6020_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_6024_ = lean_ctor_get(v_a_6020_, 1);
                v_buildTime_6025_ = lean_ctor_get(v_a_6020_, 2);
                v_isSharedCheck_6035_ = (!lean_is_exclusive(v_a_6020_)) as u8;
                if v_isSharedCheck_6035_ == 0 {
                    v___x_6027_ = v_a_6020_;
                    v_isShared_6028_ = v_isSharedCheck_6035_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_buildTime_6025_);
                    lean_inc(v_trace_6024_);
                    lean_inc(v_log_6021_);
                    lean_dec(v_a_6020_);
                    v___x_6027_ = lean_box(0);
                    v_isShared_6028_ = v_isSharedCheck_6035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6029_ = 4;
                v___x_6030_ = l_Lake_JobAction_merge(v_action_6022_, v___x_6029_);
                if v_isShared_6028_ == 0 {
                    v___x_6032_ = v___x_6027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6034_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_log_6021_);
                    lean_ctor_set(v_reuseFailAlloc_6034_, 1, v_trace_6024_);
                    lean_ctor_set(v_reuseFailAlloc_6034_, 2, v_buildTime_6025_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6034_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_6023_,
                    );
                    v___x_6032_ = v_reuseFailAlloc_6034_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_6032_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6030_,
                );
                v___x_6033_ = 0;
                v_r_6015_ = v___x_6033_;
                v___y_6016_ = v___x_6032_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(
    mut v_pkg_6049_: *mut LeanObject,
    mut v___x_6050_: *mut LeanObject,
    mut v___y_6051_: *mut LeanObject,
    mut v___y_6052_: *mut LeanObject,
    mut v___y_6053_: *mut LeanObject,
    mut v___y_6054_: *mut LeanObject,
    mut v___y_6055_: *mut LeanObject,
    mut v___y_6056_: *mut LeanObject,
    mut v___y_6057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6058_: *mut LeanObject = core::ptr::null_mut();
    v_res_6058_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(
        v_pkg_6049_,
        v___x_6050_,
        v___y_6051_,
        v___y_6052_,
        v___y_6053_,
        v___y_6054_,
        v___y_6055_,
        v___y_6056_,
    );
    lean_dec_ref(v___y_6055_);
    lean_dec(v___y_6054_);
    lean_dec(v___y_6053_);
    lean_dec(v___y_6052_);
    lean_dec_ref(v___y_6051_);
    lean_dec_ref(v___x_6050_);
    return v_res_6058_;
}
pub unsafe fn l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(
    mut v___x_6059_: *mut LeanObject,
    mut v___x_6060_: *mut LeanObject,
    mut v___x_6061_: *mut LeanObject,
    mut v___x_6062_: *mut LeanObject,
    mut v_pkg_6063_: *mut LeanObject,
    mut v___y_6064_: *mut LeanObject,
    mut v___y_6065_: *mut LeanObject,
    mut v___y_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
    mut v___y_6068_: *mut LeanObject,
    mut v___y_6069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6079_: u8 = 0;
    let mut v_task_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6084_: u8 = 0;
    let mut v_registeredJobs_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_job_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6105_: u8 = 0;
    let mut v_unused_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_pkg_6063_);
                v___f_6071_ = lean_alloc_closure(
                    l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    2,
                );
                lean_closure_set(v___f_6071_, 0, v_pkg_6063_);
                lean_closure_set(v___f_6071_, 1, v___x_6059_);
                v___x_6072_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                lean_inc(v___x_6060_);
                v___f_6073_ = lean_alloc_closure(
                    l_Lake_Package_optBarrelFacetConfig___lam__1___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___f_6073_, 0, v___x_6060_);
                lean_closure_set(v___f_6073_, 1, v___f_6071_);
                lean_closure_set(v___f_6073_, 2, v___x_6061_);
                lean_closure_set(v___f_6073_, 3, v___x_6072_);
                v___x_6074_ = l_Lake_ensureJob___redArg(
                    v___x_6060_,
                    v___f_6073_,
                    v___y_6064_,
                    v___y_6065_,
                    v___y_6066_,
                    v___y_6067_,
                    v___y_6068_,
                    v___y_6069_,
                );
                if lean_obj_tag(v___x_6074_) == 0 {
                    v_a_6075_ = lean_ctor_get(v___x_6074_, 0);
                    v_a_6076_ = lean_ctor_get(v___x_6074_, 1);
                    v_isSharedCheck_6107_ = (!lean_is_exclusive(v___x_6074_)) as u8;
                    if v_isSharedCheck_6107_ == 0 {
                        v___x_6078_ = v___x_6074_;
                        v_isShared_6079_ = v_isSharedCheck_6107_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6076_);
                        lean_inc(v_a_6075_);
                        lean_dec(v___x_6074_);
                        v___x_6078_ = lean_box(0);
                        v_isShared_6079_ = v_isSharedCheck_6107_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_pkg_6063_);
                    lean_dec(v___x_6062_);
                    return v___x_6074_;
                }
            }
            1 => {
                v_task_6080_ = lean_ctor_get(v_a_6075_, 0);
                v_kind_6081_ = lean_ctor_get(v_a_6075_, 1);
                v_isSharedCheck_6105_ = (!lean_is_exclusive(v_a_6075_)) as u8;
                if v_isSharedCheck_6105_ == 0 {
                    v_unused_6106_ = lean_ctor_get(v_a_6075_, 2);
                    lean_dec(v_unused_6106_);
                    v___x_6083_ = v_a_6075_;
                    v_isShared_6084_ = v_isSharedCheck_6105_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_6081_);
                    lean_inc(v_task_6080_);
                    lean_dec(v_a_6075_);
                    v___x_6083_ = lean_box(0);
                    v_isShared_6084_ = v_isSharedCheck_6105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_6085_ = lean_ctor_get(v___y_6068_, 3);
                v___x_6086_ = lean_st_ref_take(v_registeredJobs_6085_);
                v_baseName_6087_ = lean_ctor_get(v_pkg_6063_, 1);
                lean_inc(v_baseName_6087_);
                lean_dec_ref(v_pkg_6063_);
                v___x_6088_ = 1;
                v___x_6089_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_6087_,
                    v___x_6088_,
                );
                v___x_6090_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                v___x_6091_ = lean_string_append(v___x_6089_, v___x_6090_);
                v___x_6092_ = l_Lake_Name_eraseHead(v___x_6062_);
                v___x_6093_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_6092_,
                    v___x_6088_,
                );
                v___x_6094_ = lean_string_append(v___x_6091_, v___x_6093_);
                lean_dec_ref(v___x_6093_);
                if v_isShared_6084_ == 0 {
                    lean_ctor_set(v___x_6083_, 2, v___x_6094_);
                    v_job_6096_ = v___x_6083_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6104_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6104_, 0, v_task_6080_);
                    lean_ctor_set(v_reuseFailAlloc_6104_, 1, v_kind_6081_);
                    lean_ctor_set(v_reuseFailAlloc_6104_, 2, v___x_6094_);
                    v_job_6096_ = v_reuseFailAlloc_6104_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_6096_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6088_,
                );
                lean_inc_ref(v_job_6096_);
                v___x_6097_ = l_Lake_Job_toOpaque___redArg(v_job_6096_);
                v___x_6098_ = lean_array_push(v___x_6086_, v___x_6097_);
                v___x_6099_ = lean_st_ref_set(v_registeredJobs_6085_, v___x_6098_);
                v___x_6100_ = l_Lake_Job_renew___redArg(v_job_6096_);
                if v_isShared_6079_ == 0 {
                    lean_ctor_set(v___x_6078_, 0, v___x_6100_);
                    v___x_6102_ = v___x_6078_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6103_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6103_, 0, v___x_6100_);
                    lean_ctor_set(v_reuseFailAlloc_6103_, 1, v_a_6076_);
                    v___x_6102_ = v_reuseFailAlloc_6103_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6102_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(
    mut v___x_6108_: *mut LeanObject,
    mut v___x_6109_: *mut LeanObject,
    mut v___x_6110_: *mut LeanObject,
    mut v___x_6111_: *mut LeanObject,
    mut v_pkg_6112_: *mut LeanObject,
    mut v___y_6113_: *mut LeanObject,
    mut v___y_6114_: *mut LeanObject,
    mut v___y_6115_: *mut LeanObject,
    mut v___y_6116_: *mut LeanObject,
    mut v___y_6117_: *mut LeanObject,
    mut v___y_6118_: *mut LeanObject,
    mut v___y_6119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6120_: *mut LeanObject = core::ptr::null_mut();
    v_res_6120_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(
        v___x_6108_,
        v___x_6109_,
        v___x_6110_,
        v___x_6111_,
        v_pkg_6112_,
        v___y_6113_,
        v___y_6114_,
        v___y_6115_,
        v___y_6116_,
        v___y_6117_,
        v___y_6118_,
    );
    lean_dec_ref(v___y_6117_);
    lean_dec(v___y_6116_);
    lean_dec(v___y_6115_);
    lean_dec(v___y_6114_);
    return v_res_6120_;
}
pub unsafe fn _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6127_: *mut LeanObject = core::ptr::null_mut();
    v___x_6123_ = l_Lake_Package_optGitHubReleaseFacet;
    v___x_6124_ = lean_unsigned_to_nat(0);
    v___x_6125_ = l_Lake_instDataKindBool;
    v___x_6126_ = l_Lake_Package_optGitHubReleaseFacetConfig___closed__0;
    v___f_6127_ = lean_alloc_closure(
        l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed as *mut core::ffi::c_void,
        12,
        4,
    );
    lean_closure_set(v___f_6127_, 0, v___x_6126_);
    lean_closure_set(v___f_6127_, 1, v___x_6125_);
    lean_closure_set(v___f_6127_, 2, v___x_6124_);
    lean_closure_set(v___f_6127_, 3, v___x_6123_);
    return v___f_6127_;
}
pub unsafe fn _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2() -> *mut LeanObject {
    let mut v___f_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: u8 = 0;
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    v___f_6128_ = l_Lake_Package_optBuildCacheFacetConfig___closed__1;
    v___x_6129_ = 1;
    v___x_6130_ = l_Lake_instDataKindBool;
    v___f_6131_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_optGitHubReleaseFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once),
        _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1,
    );
    v___x_6132_ = l_Lake_Package_keyword;
    v___x_6133_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_6133_, 0, v___x_6132_);
    lean_ctor_set(v___x_6133_, 1, v___f_6131_);
    lean_ctor_set(v___x_6133_, 2, v___x_6130_);
    lean_ctor_set(v___x_6133_, 3, v___f_6128_);
    lean_ctor_set_uint8(
        v___x_6133_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_6129_,
    );
    lean_ctor_set_uint8(
        v___x_6133_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_6129_,
    );
    return v___x_6133_;
}
pub unsafe fn _init_l_Lake_Package_optGitHubReleaseFacetConfig() -> *mut LeanObject {
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    v___x_6134_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_optGitHubReleaseFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once),
        _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2,
    );
    return v___x_6134_;
}
pub unsafe fn l_Lake_Package_gitHubReleaseFacetConfig___lam__1(
    mut v_baseName_6136_: *mut LeanObject,
    mut v___x_6137_: *mut LeanObject,
    mut v_success_6138_: u8,
    mut v___y_6139_: *mut LeanObject,
    mut v___y_6140_: *mut LeanObject,
    mut v___y_6141_: *mut LeanObject,
    mut v___y_6142_: *mut LeanObject,
    mut v___y_6143_: *mut LeanObject,
    mut v___y_6144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_log_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_6150_: u8 = 0;
    let mut v_wantsRebuild_6151_: u8 = 0;
    let mut v_trace_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6156_: u8 = 0;
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: u8 = 0;
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut v_toBuildConfig_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_verbosity_6169_: u8 = 0;
    let mut v___x_6170_: u8 = 0;
    let mut v___x_6171_: u8 = 0;
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_success_6138_ == 0 {
                    v_toBuildConfig_6168_ = lean_ctor_get(v___y_6143_, 0);
                    v_verbosity_6169_ = lean_ctor_get_uint8(
                        v_toBuildConfig_6168_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                    );
                    v___x_6170_ = 2;
                    v___x_6171_ = l_Lake_instDecidableEqVerbosity(v_verbosity_6169_, v___x_6170_);
                    if v___x_6171_ == 0 {
                        lean_dec(v___x_6137_);
                        lean_dec(v_baseName_6136_);
                        v___x_6172_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
                        v_a_6147_ = v___x_6172_;
                        v_a_6148_ = v___y_6144_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6173_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1;
                        v___x_6174_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_baseName_6136_,
                                v___x_6171_,
                            );
                        v___x_6175_ = lean_string_append(v___x_6173_, v___x_6174_);
                        lean_dec_ref(v___x_6174_);
                        v___x_6176_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                        v___x_6177_ = lean_string_append(v___x_6175_, v___x_6176_);
                        v___x_6178_ = l_Lake_Name_eraseHead(v___x_6137_);
                        v___x_6179_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_6178_,
                                v___x_6171_,
                            );
                        v___x_6180_ = lean_string_append(v___x_6177_, v___x_6179_);
                        lean_dec_ref(v___x_6179_);
                        v___x_6181_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3;
                        v___x_6182_ = lean_string_append(v___x_6180_, v___x_6181_);
                        v_a_6147_ = v___x_6182_;
                        v_a_6148_ = v___y_6144_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6137_);
                    lean_dec(v_baseName_6136_);
                    v___x_6183_ = lean_box(0);
                    v___x_6184_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6184_, 0, v___x_6183_);
                    lean_ctor_set(v___x_6184_, 1, v___y_6144_);
                    return v___x_6184_;
                }
            }
            1 => {
                v_log_6149_ = lean_ctor_get(v_a_6148_, 0);
                v_action_6150_ = lean_ctor_get_uint8(
                    v_a_6148_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_6151_ = lean_ctor_get_uint8(
                    v_a_6148_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_6152_ = lean_ctor_get(v_a_6148_, 1);
                v_buildTime_6153_ = lean_ctor_get(v_a_6148_, 2);
                v_isSharedCheck_6167_ = (!lean_is_exclusive(v_a_6148_)) as u8;
                if v_isSharedCheck_6167_ == 0 {
                    v___x_6155_ = v_a_6148_;
                    v_isShared_6156_ = v_isSharedCheck_6167_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_buildTime_6153_);
                    lean_inc(v_trace_6152_);
                    lean_inc(v_log_6149_);
                    lean_dec(v_a_6148_);
                    v___x_6155_ = lean_box(0);
                    v_isShared_6156_ = v_isSharedCheck_6167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6157_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0;
                v___x_6158_ = lean_string_append(v___x_6157_, v_a_6147_);
                lean_dec_ref(v_a_6147_);
                v___x_6159_ = 3;
                v___x_6160_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_6160_, 0, v___x_6158_);
                lean_ctor_set_uint8(
                    v___x_6160_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6159_,
                );
                v___x_6161_ = lean_array_get_size(v_log_6149_);
                v___x_6162_ = lean_array_push(v_log_6149_, v___x_6160_);
                if v_isShared_6156_ == 0 {
                    lean_ctor_set(v___x_6155_, 0, v___x_6162_);
                    v___x_6164_ = v___x_6155_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6166_, 0, v___x_6162_);
                    lean_ctor_set(v_reuseFailAlloc_6166_, 1, v_trace_6152_);
                    lean_ctor_set(v_reuseFailAlloc_6166_, 2, v_buildTime_6153_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6166_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_6150_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6166_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_6151_,
                    );
                    v___x_6164_ = v_reuseFailAlloc_6166_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6165_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6165_, 0, v___x_6161_);
                lean_ctor_set(v___x_6165_, 1, v___x_6164_);
                return v___x_6165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(
    mut v_baseName_6185_: *mut LeanObject,
    mut v___x_6186_: *mut LeanObject,
    mut v_success_6187_: *mut LeanObject,
    mut v___y_6188_: *mut LeanObject,
    mut v___y_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
    mut v___y_6191_: *mut LeanObject,
    mut v___y_6192_: *mut LeanObject,
    mut v___y_6193_: *mut LeanObject,
    mut v___y_6194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_success_boxed_6195_: u8 = 0;
    let mut v_res_6196_: *mut LeanObject = core::ptr::null_mut();
    v_success_boxed_6195_ = (lean_unbox(v_success_6187_) as u8);
    v_res_6196_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(
        v_baseName_6185_,
        v___x_6186_,
        v_success_boxed_6195_,
        v___y_6188_,
        v___y_6189_,
        v___y_6190_,
        v___y_6191_,
        v___y_6192_,
        v___y_6193_,
    );
    lean_dec_ref(v___y_6192_);
    lean_dec(v___y_6191_);
    lean_dec(v___y_6190_);
    lean_dec(v___y_6189_);
    lean_dec_ref(v___y_6188_);
    return v_res_6196_;
}
pub unsafe fn l_Lake_Package_gitHubReleaseFacetConfig___lam__2(
    mut v___x_6197_: *mut LeanObject,
    mut v___x_6198_: *mut LeanObject,
    mut v___x_6199_: *mut LeanObject,
    mut v_pkg_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
    mut v___y_6203_: *mut LeanObject,
    mut v___y_6204_: *mut LeanObject,
    mut v___y_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_baseName_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6220_: u8 = 0;
    let mut v_task_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6225_: u8 = 0;
    let mut v_registeredJobs_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: u8 = 0;
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: u8 = 0;
    let mut v_job_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6246_: u8 = 0;
    let mut v_unused_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_baseName_6208_ = lean_ctor_get(v_pkg_6200_, 1);
                lean_inc_n(v_baseName_6208_, 2);
                v_keyName_6209_ = lean_ctor_get(v_pkg_6200_, 2);
                lean_inc(v___x_6197_);
                v___f_6210_ = lean_alloc_closure(
                    l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed
                        as *mut core::ffi::c_void,
                    10,
                    2,
                );
                lean_closure_set(v___f_6210_, 0, v_baseName_6208_);
                lean_closure_set(v___f_6210_, 1, v___x_6197_);
                lean_inc(v_keyName_6209_);
                v___x_6211_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6211_, 0, v_keyName_6209_);
                v___x_6212_ = l_Lake_Package_keyword;
                v___x_6213_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_6213_, 0, v___x_6211_);
                lean_ctor_set(v___x_6213_, 1, v___x_6212_);
                lean_ctor_set(v___x_6213_, 2, v_pkg_6200_);
                lean_ctor_set(v___x_6213_, 3, v___x_6197_);
                lean_inc(v___x_6198_);
                v___f_6214_ = lean_alloc_closure(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                lean_closure_set(v___f_6214_, 0, v___x_6213_);
                lean_closure_set(v___f_6214_, 1, v___x_6198_);
                lean_closure_set(v___f_6214_, 2, v___f_6210_);
                v___x_6215_ = l_Lake_ensureJob___redArg(
                    v___x_6198_,
                    v___f_6214_,
                    v___y_6201_,
                    v___y_6202_,
                    v___y_6203_,
                    v___y_6204_,
                    v___y_6205_,
                    v___y_6206_,
                );
                if lean_obj_tag(v___x_6215_) == 0 {
                    v_a_6216_ = lean_ctor_get(v___x_6215_, 0);
                    v_a_6217_ = lean_ctor_get(v___x_6215_, 1);
                    v_isSharedCheck_6248_ = (!lean_is_exclusive(v___x_6215_)) as u8;
                    if v_isSharedCheck_6248_ == 0 {
                        v___x_6219_ = v___x_6215_;
                        v_isShared_6220_ = v_isSharedCheck_6248_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6217_);
                        lean_inc(v_a_6216_);
                        lean_dec(v___x_6215_);
                        v___x_6219_ = lean_box(0);
                        v_isShared_6220_ = v_isSharedCheck_6248_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_baseName_6208_);
                    lean_dec(v___x_6199_);
                    return v___x_6215_;
                }
            }
            1 => {
                v_task_6221_ = lean_ctor_get(v_a_6216_, 0);
                v_kind_6222_ = lean_ctor_get(v_a_6216_, 1);
                v_isSharedCheck_6246_ = (!lean_is_exclusive(v_a_6216_)) as u8;
                if v_isSharedCheck_6246_ == 0 {
                    v_unused_6247_ = lean_ctor_get(v_a_6216_, 2);
                    lean_dec(v_unused_6247_);
                    v___x_6224_ = v_a_6216_;
                    v_isShared_6225_ = v_isSharedCheck_6246_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_kind_6222_);
                    lean_inc(v_task_6221_);
                    lean_dec(v_a_6216_);
                    v___x_6224_ = lean_box(0);
                    v_isShared_6225_ = v_isSharedCheck_6246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_6226_ = lean_ctor_get(v___y_6205_, 3);
                v___x_6227_ = lean_st_ref_take(v_registeredJobs_6226_);
                v___x_6228_ = 1;
                v___x_6229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_baseName_6208_,
                    v___x_6228_,
                );
                v___x_6230_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2;
                v___x_6231_ = lean_string_append(v___x_6229_, v___x_6230_);
                v___x_6232_ = l_Lake_Name_eraseHead(v___x_6199_);
                v___x_6233_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_6232_,
                    v___x_6228_,
                );
                v___x_6234_ = lean_string_append(v___x_6231_, v___x_6233_);
                lean_dec_ref(v___x_6233_);
                v___x_6235_ = 0;
                if v_isShared_6225_ == 0 {
                    lean_ctor_set(v___x_6224_, 2, v___x_6234_);
                    v_job_6237_ = v___x_6224_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6245_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6245_, 0, v_task_6221_);
                    lean_ctor_set(v_reuseFailAlloc_6245_, 1, v_kind_6222_);
                    lean_ctor_set(v_reuseFailAlloc_6245_, 2, v___x_6234_);
                    v_job_6237_ = v_reuseFailAlloc_6245_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v_job_6237_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6235_,
                );
                lean_inc_ref(v_job_6237_);
                v___x_6238_ = l_Lake_Job_toOpaque___redArg(v_job_6237_);
                v___x_6239_ = lean_array_push(v___x_6227_, v___x_6238_);
                v___x_6240_ = lean_st_ref_set(v_registeredJobs_6226_, v___x_6239_);
                v___x_6241_ = l_Lake_Job_renew___redArg(v_job_6237_);
                if v_isShared_6220_ == 0 {
                    lean_ctor_set(v___x_6219_, 0, v___x_6241_);
                    v___x_6243_ = v___x_6219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6244_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6244_, 0, v___x_6241_);
                    lean_ctor_set(v_reuseFailAlloc_6244_, 1, v_a_6217_);
                    v___x_6243_ = v_reuseFailAlloc_6244_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(
    mut v___x_6249_: *mut LeanObject,
    mut v___x_6250_: *mut LeanObject,
    mut v___x_6251_: *mut LeanObject,
    mut v_pkg_6252_: *mut LeanObject,
    mut v___y_6253_: *mut LeanObject,
    mut v___y_6254_: *mut LeanObject,
    mut v___y_6255_: *mut LeanObject,
    mut v___y_6256_: *mut LeanObject,
    mut v___y_6257_: *mut LeanObject,
    mut v___y_6258_: *mut LeanObject,
    mut v___y_6259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6260_: *mut LeanObject = core::ptr::null_mut();
    v_res_6260_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(
        v___x_6249_,
        v___x_6250_,
        v___x_6251_,
        v_pkg_6252_,
        v___y_6253_,
        v___y_6254_,
        v___y_6255_,
        v___y_6256_,
        v___y_6257_,
        v___y_6258_,
    );
    lean_dec_ref(v___y_6257_);
    lean_dec(v___y_6256_);
    lean_dec(v___y_6255_);
    lean_dec(v___y_6254_);
    return v_res_6260_;
}
pub unsafe fn _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0() -> *mut LeanObject {
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6264_: *mut LeanObject = core::ptr::null_mut();
    v___x_6261_ = l_Lake_Package_gitHubReleaseFacet;
    v___x_6262_ = l_Lake_instDataKindUnit;
    v___x_6263_ = l_Lake_Package_optGitHubReleaseFacet;
    v___f_6264_ = lean_alloc_closure(
        l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    lean_closure_set(v___f_6264_, 0, v___x_6263_);
    lean_closure_set(v___f_6264_, 1, v___x_6262_);
    lean_closure_set(v___f_6264_, 2, v___x_6261_);
    return v___f_6264_;
}
pub unsafe fn _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1() -> *mut LeanObject {
    let mut v___f_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: u8 = 0;
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    v___f_6265_ = l_Lake_Package_extraDepFacetConfig___closed__0;
    v___x_6266_ = 1;
    v___x_6267_ = l_Lake_instDataKindUnit;
    v___f_6268_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_gitHubReleaseFacetConfig___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once),
        _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0,
    );
    v___x_6269_ = l_Lake_Package_keyword;
    v___x_6270_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_6270_, 0, v___x_6269_);
    lean_ctor_set(v___x_6270_, 1, v___f_6268_);
    lean_ctor_set(v___x_6270_, 2, v___x_6267_);
    lean_ctor_set(v___x_6270_, 3, v___f_6265_);
    lean_ctor_set_uint8(
        v___x_6270_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v___x_6266_,
    );
    lean_ctor_set_uint8(
        v___x_6270_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_6266_,
    );
    return v___x_6270_;
}
pub unsafe fn _init_l_Lake_Package_gitHubReleaseFacetConfig() -> *mut LeanObject {
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    v___x_6271_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_gitHubReleaseFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once),
        _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1,
    );
    return v___x_6271_;
}
pub unsafe fn l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(
    mut v_build_6272_: *mut LeanObject,
    mut v_x_6273_: u8,
    mut v___y_6274_: *mut LeanObject,
    mut v___y_6275_: *mut LeanObject,
    mut v___y_6276_: *mut LeanObject,
    mut v___y_6277_: *mut LeanObject,
    mut v___y_6278_: *mut LeanObject,
    mut v___y_6279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_log_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_6282_: u8 = 0;
    let mut v_wantsRebuild_6283_: u8 = 0;
    let mut v_buildTime_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6287_: u8 = 0;
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6293_: u8 = 0;
    let mut v_unused_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_6281_ = lean_ctor_get(v___y_6279_, 0);
                v_action_6282_ = lean_ctor_get_uint8(
                    v___y_6279_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_6283_ = lean_ctor_get_uint8(
                    v___y_6279_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_6284_ = lean_ctor_get(v___y_6279_, 2);
                v_isSharedCheck_6293_ = (!lean_is_exclusive(v___y_6279_)) as u8;
                if v_isSharedCheck_6293_ == 0 {
                    v_unused_6294_ = lean_ctor_get(v___y_6279_, 1);
                    lean_dec(v_unused_6294_);
                    v___x_6286_ = v___y_6279_;
                    v_isShared_6287_ = v_isSharedCheck_6293_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buildTime_6284_);
                    lean_inc(v_log_6281_);
                    lean_dec(v___y_6279_);
                    v___x_6286_ = lean_box(0);
                    v_isShared_6287_ = v_isSharedCheck_6293_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6288_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                if v_isShared_6287_ == 0 {
                    lean_ctor_set(v___x_6286_, 1, v___x_6288_);
                    v___x_6290_ = v___x_6286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6292_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6292_, 0, v_log_6281_);
                    lean_ctor_set(v_reuseFailAlloc_6292_, 1, v___x_6288_);
                    lean_ctor_set(v_reuseFailAlloc_6292_, 2, v_buildTime_6284_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6292_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_6282_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6292_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_6283_,
                    );
                    v___x_6290_ = v_reuseFailAlloc_6292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___y_6278_);
                lean_inc(v___y_6277_);
                lean_inc(v___y_6276_);
                lean_inc(v___y_6275_);
                v___x_6291_ = lean_apply_7(
                    v_build_6272_,
                    v___y_6274_,
                    v___y_6275_,
                    v___y_6276_,
                    v___y_6277_,
                    v___y_6278_,
                    v___x_6290_,
                    lean_box(0),
                );
                return v___x_6291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(
    mut v_build_6295_: *mut LeanObject,
    mut v_x_6296_: *mut LeanObject,
    mut v___y_6297_: *mut LeanObject,
    mut v___y_6298_: *mut LeanObject,
    mut v___y_6299_: *mut LeanObject,
    mut v___y_6300_: *mut LeanObject,
    mut v___y_6301_: *mut LeanObject,
    mut v___y_6302_: *mut LeanObject,
    mut v___y_6303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1923__boxed_6304_: u8 = 0;
    let mut v_res_6305_: *mut LeanObject = core::ptr::null_mut();
    v_x_1923__boxed_6304_ = (lean_unbox(v_x_6296_) as u8);
    v_res_6305_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(
        v_build_6295_,
        v_x_1923__boxed_6304_,
        v___y_6297_,
        v___y_6298_,
        v___y_6299_,
        v___y_6300_,
        v___y_6301_,
        v___y_6302_,
    );
    lean_dec_ref(v___y_6301_);
    lean_dec(v___y_6300_);
    lean_dec(v___y_6299_);
    lean_dec(v___y_6298_);
    return v_res_6305_;
}
pub unsafe fn l_Lake_Package_afterBuildCacheAsync___redArg(
    mut v_self_6306_: *mut LeanObject,
    mut v_build_6307_: *mut LeanObject,
    mut v_a_6308_: *mut LeanObject,
    mut v_a_6309_: *mut LeanObject,
    mut v_a_6310_: *mut LeanObject,
    mut v_a_6311_: *mut LeanObject,
    mut v_a_6312_: *mut LeanObject,
    mut v_a_6313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_wsIdx_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: u8 = 0;
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6323_: u8 = 0;
    let mut v___f_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6331_: u8 = 0;
    let mut v_a_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6336_: u8 = 0;
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v___x_6341_: u8 = 0;
    let mut v___x_6342_: u8 = 0;
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6350_: u8 = 0;
    let mut v_log_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6355_: u8 = 0;
    let mut v_a_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6360_: u8 = 0;
    let mut v_log_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_wsIdx_6315_ = lean_ctor_get(v_self_6306_, 0);
                v___x_6316_ = lean_unsigned_to_nat(0);
                v___x_6317_ = lean_nat_dec_eq(v_wsIdx_6315_, v___x_6316_);
                if v___x_6317_ == 0 {
                    lean_inc_ref(v_a_6308_);
                    v___x_6318_ =
                        l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(
                            v_self_6306_,
                            v_a_6308_,
                            v_a_6309_,
                            v_a_6310_,
                            v_a_6311_,
                            v_a_6312_,
                            v_a_6313_,
                        );
                    if lean_obj_tag(v___x_6318_) == 0 {
                        v_a_6319_ = lean_ctor_get(v___x_6318_, 0);
                        v_a_6320_ = lean_ctor_get(v___x_6318_, 1);
                        v_isSharedCheck_6331_ = (!lean_is_exclusive(v___x_6318_)) as u8;
                        if v_isSharedCheck_6331_ == 0 {
                            v___x_6322_ = v___x_6318_;
                            v_isShared_6323_ = v_isSharedCheck_6331_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6320_);
                            lean_inc(v_a_6319_);
                            lean_dec(v___x_6318_);
                            v___x_6322_ = lean_box(0);
                            v_isShared_6323_ = v_isSharedCheck_6331_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_6308_);
                        lean_dec_ref(v_build_6307_);
                        v_a_6332_ = lean_ctor_get(v___x_6318_, 0);
                        v_a_6333_ = lean_ctor_get(v___x_6318_, 1);
                        v_isSharedCheck_6340_ = (!lean_is_exclusive(v___x_6318_)) as u8;
                        if v_isSharedCheck_6340_ == 0 {
                            v___x_6335_ = v___x_6318_;
                            v_isShared_6336_ = v_isSharedCheck_6340_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6333_);
                            lean_inc(v_a_6332_);
                            lean_dec(v___x_6318_);
                            v___x_6335_ = lean_box(0);
                            v_isShared_6336_ = v_isSharedCheck_6340_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_self_6306_);
                    v___x_6341_ = 0;
                    v___x_6342_ = 0;
                    v___x_6343_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                    v___x_6344_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v___x_6344_, 0, v_a_6313_);
                    lean_ctor_set(v___x_6344_, 1, v___x_6343_);
                    lean_ctor_set(v___x_6344_, 2, v___x_6316_);
                    lean_ctor_set_uint8(
                        v___x_6344_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_6341_,
                    );
                    lean_ctor_set_uint8(
                        v___x_6344_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v___x_6342_,
                    );
                    lean_inc_ref(v_a_6312_);
                    lean_inc(v_a_6311_);
                    lean_inc(v_a_6310_);
                    lean_inc(v_a_6309_);
                    v___x_6345_ = lean_apply_7(
                        v_build_6307_,
                        v_a_6308_,
                        v_a_6309_,
                        v_a_6310_,
                        v_a_6311_,
                        v_a_6312_,
                        v___x_6344_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_6345_) == 0 {
                        v_a_6346_ = lean_ctor_get(v___x_6345_, 1);
                        v_a_6347_ = lean_ctor_get(v___x_6345_, 0);
                        v_isSharedCheck_6355_ = (!lean_is_exclusive(v___x_6345_)) as u8;
                        if v_isSharedCheck_6355_ == 0 {
                            v___x_6349_ = v___x_6345_;
                            v_isShared_6350_ = v_isSharedCheck_6355_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_6346_);
                            lean_inc(v_a_6347_);
                            lean_dec(v___x_6345_);
                            v___x_6349_ = lean_box(0);
                            v_isShared_6350_ = v_isSharedCheck_6355_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_6356_ = lean_ctor_get(v___x_6345_, 1);
                        v_a_6357_ = lean_ctor_get(v___x_6345_, 0);
                        v_isSharedCheck_6365_ = (!lean_is_exclusive(v___x_6345_)) as u8;
                        if v_isSharedCheck_6365_ == 0 {
                            v___x_6359_ = v___x_6345_;
                            v_isShared_6360_ = v_isSharedCheck_6365_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6356_);
                            lean_inc(v_a_6357_);
                            lean_dec(v___x_6345_);
                            v___x_6359_ = lean_box(0);
                            v_isShared_6360_ = v_isSharedCheck_6365_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___f_6324_ = lean_alloc_closure(
                    l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    1,
                );
                lean_closure_set(v___f_6324_, 0, v_build_6307_);
                v___x_6325_ = lean_box(0);
                v___x_6326_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                v___x_6327_ = l_Lake_Job_bindM___redArg(
                    v___x_6325_,
                    v_a_6319_,
                    v___f_6324_,
                    v___x_6316_,
                    v___x_6317_,
                    v_a_6308_,
                    v_a_6309_,
                    v_a_6310_,
                    v_a_6311_,
                    v_a_6312_,
                    v___x_6326_,
                );
                if v_isShared_6323_ == 0 {
                    lean_ctor_set(v___x_6322_, 0, v___x_6327_);
                    v___x_6329_ = v___x_6322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6330_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6330_, 0, v___x_6327_);
                    lean_ctor_set(v_reuseFailAlloc_6330_, 1, v_a_6320_);
                    v___x_6329_ = v_reuseFailAlloc_6330_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6329_;
            }
            3 => {
                if v_isShared_6336_ == 0 {
                    v___x_6338_ = v___x_6335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6339_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6332_);
                    lean_ctor_set(v_reuseFailAlloc_6339_, 1, v_a_6333_);
                    v___x_6338_ = v_reuseFailAlloc_6339_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6338_;
            }
            5 => {
                v_log_6351_ = lean_ctor_get(v_a_6346_, 0);
                lean_inc_ref(v_log_6351_);
                lean_dec(v_a_6346_);
                if v_isShared_6350_ == 0 {
                    lean_ctor_set(v___x_6349_, 1, v_log_6351_);
                    v___x_6353_ = v___x_6349_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6354_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6354_, 0, v_a_6347_);
                    lean_ctor_set(v_reuseFailAlloc_6354_, 1, v_log_6351_);
                    v___x_6353_ = v_reuseFailAlloc_6354_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6353_;
            }
            7 => {
                v_log_6361_ = lean_ctor_get(v_a_6356_, 0);
                lean_inc_ref(v_log_6361_);
                lean_dec(v_a_6356_);
                if v_isShared_6360_ == 0 {
                    lean_ctor_set(v___x_6359_, 1, v_log_6361_);
                    v___x_6363_ = v___x_6359_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6364_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6364_, 0, v_a_6357_);
                    lean_ctor_set(v_reuseFailAlloc_6364_, 1, v_log_6361_);
                    v___x_6363_ = v_reuseFailAlloc_6364_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_afterBuildCacheAsync___redArg___boxed(
    mut v_self_6366_: *mut LeanObject,
    mut v_build_6367_: *mut LeanObject,
    mut v_a_6368_: *mut LeanObject,
    mut v_a_6369_: *mut LeanObject,
    mut v_a_6370_: *mut LeanObject,
    mut v_a_6371_: *mut LeanObject,
    mut v_a_6372_: *mut LeanObject,
    mut v_a_6373_: *mut LeanObject,
    mut v_a_6374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6375_: *mut LeanObject = core::ptr::null_mut();
    v_res_6375_ = l_Lake_Package_afterBuildCacheAsync___redArg(
        v_self_6366_,
        v_build_6367_,
        v_a_6368_,
        v_a_6369_,
        v_a_6370_,
        v_a_6371_,
        v_a_6372_,
        v_a_6373_,
    );
    lean_dec_ref(v_a_6372_);
    lean_dec(v_a_6371_);
    lean_dec(v_a_6370_);
    lean_dec(v_a_6369_);
    return v_res_6375_;
}
pub unsafe fn l_Lake_Package_afterBuildCacheAsync(
    mut v_00_u03b1_6376_: *mut LeanObject,
    mut v_self_6377_: *mut LeanObject,
    mut v_build_6378_: *mut LeanObject,
    mut v_a_6379_: *mut LeanObject,
    mut v_a_6380_: *mut LeanObject,
    mut v_a_6381_: *mut LeanObject,
    mut v_a_6382_: *mut LeanObject,
    mut v_a_6383_: *mut LeanObject,
    mut v_a_6384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    v___x_6386_ = l_Lake_Package_afterBuildCacheAsync___redArg(
        v_self_6377_,
        v_build_6378_,
        v_a_6379_,
        v_a_6380_,
        v_a_6381_,
        v_a_6382_,
        v_a_6383_,
        v_a_6384_,
    );
    return v___x_6386_;
}
pub unsafe fn l_Lake_Package_afterBuildCacheAsync___boxed(
    mut v_00_u03b1_6387_: *mut LeanObject,
    mut v_self_6388_: *mut LeanObject,
    mut v_build_6389_: *mut LeanObject,
    mut v_a_6390_: *mut LeanObject,
    mut v_a_6391_: *mut LeanObject,
    mut v_a_6392_: *mut LeanObject,
    mut v_a_6393_: *mut LeanObject,
    mut v_a_6394_: *mut LeanObject,
    mut v_a_6395_: *mut LeanObject,
    mut v_a_6396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6397_: *mut LeanObject = core::ptr::null_mut();
    v_res_6397_ = l_Lake_Package_afterBuildCacheAsync(
        v_00_u03b1_6387_,
        v_self_6388_,
        v_build_6389_,
        v_a_6390_,
        v_a_6391_,
        v_a_6392_,
        v_a_6393_,
        v_a_6394_,
        v_a_6395_,
    );
    lean_dec_ref(v_a_6394_);
    lean_dec(v_a_6393_);
    lean_dec(v_a_6392_);
    lean_dec(v_a_6391_);
    return v_res_6397_;
}
pub unsafe fn l_Lake_Package_afterBuildCacheSync___redArg___lam__0(
    mut v_build_6398_: *mut LeanObject,
    mut v_x_6399_: u8,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
    mut v___y_6402_: *mut LeanObject,
    mut v___y_6403_: *mut LeanObject,
    mut v___y_6404_: *mut LeanObject,
    mut v___y_6405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_log_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_6408_: u8 = 0;
    let mut v_wantsRebuild_6409_: u8 = 0;
    let mut v_buildTime_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6413_: u8 = 0;
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6419_: u8 = 0;
    let mut v_unused_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_6407_ = lean_ctor_get(v___y_6405_, 0);
                v_action_6408_ = lean_ctor_get_uint8(
                    v___y_6405_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_6409_ = lean_ctor_get_uint8(
                    v___y_6405_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_6410_ = lean_ctor_get(v___y_6405_, 2);
                v_isSharedCheck_6419_ = (!lean_is_exclusive(v___y_6405_)) as u8;
                if v_isSharedCheck_6419_ == 0 {
                    v_unused_6420_ = lean_ctor_get(v___y_6405_, 1);
                    lean_dec(v_unused_6420_);
                    v___x_6412_ = v___y_6405_;
                    v_isShared_6413_ = v_isSharedCheck_6419_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buildTime_6410_);
                    lean_inc(v_log_6407_);
                    lean_dec(v___y_6405_);
                    v___x_6412_ = lean_box(0);
                    v_isShared_6413_ = v_isSharedCheck_6419_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6414_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                if v_isShared_6413_ == 0 {
                    lean_ctor_set(v___x_6412_, 1, v___x_6414_);
                    v___x_6416_ = v___x_6412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6418_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6418_, 0, v_log_6407_);
                    lean_ctor_set(v_reuseFailAlloc_6418_, 1, v___x_6414_);
                    lean_ctor_set(v_reuseFailAlloc_6418_, 2, v_buildTime_6410_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6418_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_6408_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6418_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_6409_,
                    );
                    v___x_6416_ = v_reuseFailAlloc_6418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___y_6404_);
                lean_inc(v___y_6403_);
                lean_inc(v___y_6402_);
                lean_inc(v___y_6401_);
                v___x_6417_ = lean_apply_7(
                    v_build_6398_,
                    v___y_6400_,
                    v___y_6401_,
                    v___y_6402_,
                    v___y_6403_,
                    v___y_6404_,
                    v___x_6416_,
                    lean_box(0),
                );
                return v___x_6417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(
    mut v_build_6421_: *mut LeanObject,
    mut v_x_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
    mut v___y_6426_: *mut LeanObject,
    mut v___y_6427_: *mut LeanObject,
    mut v___y_6428_: *mut LeanObject,
    mut v___y_6429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1946__boxed_6430_: u8 = 0;
    let mut v_res_6431_: *mut LeanObject = core::ptr::null_mut();
    v_x_1946__boxed_6430_ = (lean_unbox(v_x_6422_) as u8);
    v_res_6431_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(
        v_build_6421_,
        v_x_1946__boxed_6430_,
        v___y_6423_,
        v___y_6424_,
        v___y_6425_,
        v___y_6426_,
        v___y_6427_,
        v___y_6428_,
    );
    lean_dec_ref(v___y_6427_);
    lean_dec(v___y_6426_);
    lean_dec(v___y_6425_);
    lean_dec(v___y_6424_);
    return v_res_6431_;
}
pub unsafe fn l_Lake_Package_afterBuildCacheSync___redArg(
    mut v_self_6432_: *mut LeanObject,
    mut v_build_6433_: *mut LeanObject,
    mut v_a_6434_: *mut LeanObject,
    mut v_a_6435_: *mut LeanObject,
    mut v_a_6436_: *mut LeanObject,
    mut v_a_6437_: *mut LeanObject,
    mut v_a_6438_: *mut LeanObject,
    mut v_a_6439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_wsIdx_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: u8 = 0;
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6449_: u8 = 0;
    let mut v___f_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6457_: u8 = 0;
    let mut v_a_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6462_: u8 = 0;
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6466_: u8 = 0;
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_wsIdx_6441_ = lean_ctor_get(v_self_6432_, 0);
                v___x_6442_ = lean_unsigned_to_nat(0);
                v___x_6443_ = lean_nat_dec_eq(v_wsIdx_6441_, v___x_6442_);
                if v___x_6443_ == 0 {
                    lean_inc_ref(v_a_6434_);
                    v___x_6444_ =
                        l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(
                            v_self_6432_,
                            v_a_6434_,
                            v_a_6435_,
                            v_a_6436_,
                            v_a_6437_,
                            v_a_6438_,
                            v_a_6439_,
                        );
                    if lean_obj_tag(v___x_6444_) == 0 {
                        v_a_6445_ = lean_ctor_get(v___x_6444_, 0);
                        v_a_6446_ = lean_ctor_get(v___x_6444_, 1);
                        v_isSharedCheck_6457_ = (!lean_is_exclusive(v___x_6444_)) as u8;
                        if v_isSharedCheck_6457_ == 0 {
                            v___x_6448_ = v___x_6444_;
                            v_isShared_6449_ = v_isSharedCheck_6457_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6446_);
                            lean_inc(v_a_6445_);
                            lean_dec(v___x_6444_);
                            v___x_6448_ = lean_box(0);
                            v_isShared_6449_ = v_isSharedCheck_6457_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_6434_);
                        lean_dec_ref(v_build_6433_);
                        v_a_6458_ = lean_ctor_get(v___x_6444_, 0);
                        v_a_6459_ = lean_ctor_get(v___x_6444_, 1);
                        v_isSharedCheck_6466_ = (!lean_is_exclusive(v___x_6444_)) as u8;
                        if v_isSharedCheck_6466_ == 0 {
                            v___x_6461_ = v___x_6444_;
                            v_isShared_6462_ = v_isSharedCheck_6466_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6459_);
                            lean_inc(v_a_6458_);
                            lean_dec(v___x_6444_);
                            v___x_6461_ = lean_box(0);
                            v_isShared_6462_ = v_isSharedCheck_6466_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_self_6432_);
                    v___x_6467_ = lean_box(0);
                    v___x_6468_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1;
                    v___x_6469_ = l_Lake_Job_async___redArg(
                        v___x_6467_,
                        v_build_6433_,
                        v___x_6442_,
                        v___x_6468_,
                        v_a_6434_,
                        v_a_6435_,
                        v_a_6436_,
                        v_a_6437_,
                        v_a_6438_,
                    );
                    v___x_6470_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6470_, 0, v___x_6469_);
                    lean_ctor_set(v___x_6470_, 1, v_a_6439_);
                    return v___x_6470_;
                }
            }
            1 => {
                v___f_6450_ = lean_alloc_closure(
                    l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    1,
                );
                lean_closure_set(v___f_6450_, 0, v_build_6433_);
                v___x_6451_ = lean_box(0);
                v___x_6452_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once), _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
                v___x_6453_ = l_Lake_Job_mapM___redArg(
                    v___x_6451_,
                    v_a_6445_,
                    v___f_6450_,
                    v___x_6442_,
                    v___x_6443_,
                    v_a_6434_,
                    v_a_6435_,
                    v_a_6436_,
                    v_a_6437_,
                    v_a_6438_,
                    v___x_6452_,
                );
                if v_isShared_6449_ == 0 {
                    lean_ctor_set(v___x_6448_, 0, v___x_6453_);
                    v___x_6455_ = v___x_6448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6456_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6456_, 0, v___x_6453_);
                    lean_ctor_set(v_reuseFailAlloc_6456_, 1, v_a_6446_);
                    v___x_6455_ = v_reuseFailAlloc_6456_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6455_;
            }
            3 => {
                if v_isShared_6462_ == 0 {
                    v___x_6464_ = v___x_6461_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6465_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6465_, 0, v_a_6458_);
                    lean_ctor_set(v_reuseFailAlloc_6465_, 1, v_a_6459_);
                    v___x_6464_ = v_reuseFailAlloc_6465_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6464_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_afterBuildCacheSync___redArg___boxed(
    mut v_self_6471_: *mut LeanObject,
    mut v_build_6472_: *mut LeanObject,
    mut v_a_6473_: *mut LeanObject,
    mut v_a_6474_: *mut LeanObject,
    mut v_a_6475_: *mut LeanObject,
    mut v_a_6476_: *mut LeanObject,
    mut v_a_6477_: *mut LeanObject,
    mut v_a_6478_: *mut LeanObject,
    mut v_a_6479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6480_: *mut LeanObject = core::ptr::null_mut();
    v_res_6480_ = l_Lake_Package_afterBuildCacheSync___redArg(
        v_self_6471_,
        v_build_6472_,
        v_a_6473_,
        v_a_6474_,
        v_a_6475_,
        v_a_6476_,
        v_a_6477_,
        v_a_6478_,
    );
    lean_dec_ref(v_a_6477_);
    lean_dec(v_a_6476_);
    lean_dec(v_a_6475_);
    lean_dec(v_a_6474_);
    return v_res_6480_;
}
pub unsafe fn l_Lake_Package_afterBuildCacheSync(
    mut v_00_u03b1_6481_: *mut LeanObject,
    mut v_self_6482_: *mut LeanObject,
    mut v_build_6483_: *mut LeanObject,
    mut v_a_6484_: *mut LeanObject,
    mut v_a_6485_: *mut LeanObject,
    mut v_a_6486_: *mut LeanObject,
    mut v_a_6487_: *mut LeanObject,
    mut v_a_6488_: *mut LeanObject,
    mut v_a_6489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    v___x_6491_ = l_Lake_Package_afterBuildCacheSync___redArg(
        v_self_6482_,
        v_build_6483_,
        v_a_6484_,
        v_a_6485_,
        v_a_6486_,
        v_a_6487_,
        v_a_6488_,
        v_a_6489_,
    );
    return v___x_6491_;
}
pub unsafe fn l_Lake_Package_afterBuildCacheSync___boxed(
    mut v_00_u03b1_6492_: *mut LeanObject,
    mut v_self_6493_: *mut LeanObject,
    mut v_build_6494_: *mut LeanObject,
    mut v_a_6495_: *mut LeanObject,
    mut v_a_6496_: *mut LeanObject,
    mut v_a_6497_: *mut LeanObject,
    mut v_a_6498_: *mut LeanObject,
    mut v_a_6499_: *mut LeanObject,
    mut v_a_6500_: *mut LeanObject,
    mut v_a_6501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6502_: *mut LeanObject = core::ptr::null_mut();
    v_res_6502_ = l_Lake_Package_afterBuildCacheSync(
        v_00_u03b1_6492_,
        v_self_6493_,
        v_build_6494_,
        v_a_6495_,
        v_a_6496_,
        v_a_6497_,
        v_a_6498_,
        v_a_6499_,
        v_a_6500_,
    );
    lean_dec_ref(v_a_6499_);
    lean_dec(v_a_6498_);
    lean_dec(v_a_6497_);
    lean_dec(v_a_6496_);
    return v_res_6502_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
    mut v_k_6503_: *mut LeanObject,
    mut v_v_6504_: *mut LeanObject,
    mut v_t_6505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6513_: u8 = 0;
    let mut v___x_6514_: u8 = 0;
    let mut v_impl_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: u8 = 0;
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6533_: u8 = 0;
    let mut v_size_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: u8 = 0;
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6545_: u8 = 0;
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6571_: u8 = 0;
    let mut v_unused_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6585_: u8 = 0;
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6589_: u8 = 0;
    let mut v_unused_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6596_: u8 = 0;
    let mut v_unused_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6608_: u8 = 0;
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6616_: u8 = 0;
    let mut v_unused_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6624_: u8 = 0;
    let mut v_k_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6629_: u8 = 0;
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6640_: u8 = 0;
    let mut v_unused_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6644_: u8 = 0;
    let mut v_unused_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: u8 = 0;
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6673_: u8 = 0;
    let mut v_size_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: u8 = 0;
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6685_: u8 = 0;
    let mut v___x_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6710_: u8 = 0;
    let mut v_unused_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6723_: u8 = 0;
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6727_: u8 = 0;
    let mut v_unused_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6734_: u8 = 0;
    let mut v_unused_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6746_: u8 = 0;
    let mut v_k_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6751_: u8 = 0;
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6762_: u8 = 0;
    let mut v_unused_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6766_: u8 = 0;
    let mut v_unused_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6774_: u8 = 0;
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6782_: u8 = 0;
    let mut v_unused_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6790_: u8 = 0;
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_6505_) == 0 {
                    v_size_6506_ = lean_ctor_get(v_t_6505_, 0);
                    v_k_6507_ = lean_ctor_get(v_t_6505_, 1);
                    v_v_6508_ = lean_ctor_get(v_t_6505_, 2);
                    v_l_6509_ = lean_ctor_get(v_t_6505_, 3);
                    v_r_6510_ = lean_ctor_get(v_t_6505_, 4);
                    v_isSharedCheck_6790_ = (!lean_is_exclusive(v_t_6505_)) as u8;
                    if v_isSharedCheck_6790_ == 0 {
                        v___x_6512_ = v_t_6505_;
                        v_isShared_6513_ = v_isSharedCheck_6790_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_6510_);
                        lean_inc(v_l_6509_);
                        lean_inc(v_v_6508_);
                        lean_inc(v_k_6507_);
                        lean_inc(v_size_6506_);
                        lean_dec(v_t_6505_);
                        v___x_6512_ = lean_box(0);
                        v_isShared_6513_ = v_isSharedCheck_6790_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6791_ = lean_unsigned_to_nat(1);
                    v___x_6792_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_6792_, 0, v___x_6791_);
                    lean_ctor_set(v___x_6792_, 1, v_k_6503_);
                    lean_ctor_set(v___x_6792_, 2, v_v_6504_);
                    lean_ctor_set(v___x_6792_, 3, v_t_6505_);
                    lean_ctor_set(v___x_6792_, 4, v_t_6505_);
                    return v___x_6792_;
                }
            }
            1 => {
                v___x_6514_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6503_, v_k_6507_);
                match v___x_6514_ {
                    0 => {
                        lean_dec(v_size_6506_);
                        v_impl_6515_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_6503_, v_v_6504_, v_l_6509_);
                        v___x_6516_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_6510_) == 0 {
                            v_size_6517_ = lean_ctor_get(v_r_6510_, 0);
                            v_size_6518_ = lean_ctor_get(v_impl_6515_, 0);
                            lean_inc(v_size_6518_);
                            v_k_6519_ = lean_ctor_get(v_impl_6515_, 1);
                            lean_inc(v_k_6519_);
                            v_v_6520_ = lean_ctor_get(v_impl_6515_, 2);
                            lean_inc(v_v_6520_);
                            v_l_6521_ = lean_ctor_get(v_impl_6515_, 3);
                            lean_inc(v_l_6521_);
                            v_r_6522_ = lean_ctor_get(v_impl_6515_, 4);
                            lean_inc(v_r_6522_);
                            v___x_6523_ = lean_unsigned_to_nat(3);
                            v___x_6524_ = lean_nat_mul(v___x_6523_, v_size_6517_);
                            v___x_6525_ = lean_nat_dec_lt(v___x_6524_, v_size_6518_);
                            lean_dec(v___x_6524_);
                            if v___x_6525_ == 0 {
                                lean_dec(v_r_6522_);
                                lean_dec(v_l_6521_);
                                lean_dec(v_v_6520_);
                                lean_dec(v_k_6519_);
                                v___x_6526_ = lean_nat_add(v___x_6516_, v_size_6518_);
                                lean_dec(v_size_6518_);
                                v___x_6527_ = lean_nat_add(v___x_6526_, v_size_6517_);
                                lean_dec(v___x_6526_);
                                if v_isShared_6513_ == 0 {
                                    lean_ctor_set(v___x_6512_, 3, v_impl_6515_);
                                    lean_ctor_set(v___x_6512_, 0, v___x_6527_);
                                    v___x_6529_ = v___x_6512_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6530_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6530_, 0, v___x_6527_);
                                    lean_ctor_set(v_reuseFailAlloc_6530_, 1, v_k_6507_);
                                    lean_ctor_set(v_reuseFailAlloc_6530_, 2, v_v_6508_);
                                    lean_ctor_set(v_reuseFailAlloc_6530_, 3, v_impl_6515_);
                                    lean_ctor_set(v_reuseFailAlloc_6530_, 4, v_r_6510_);
                                    v___x_6529_ = v_reuseFailAlloc_6530_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_6596_ = (!lean_is_exclusive(v_impl_6515_)) as u8;
                                if v_isSharedCheck_6596_ == 0 {
                                    v_unused_6597_ = lean_ctor_get(v_impl_6515_, 4);
                                    lean_dec(v_unused_6597_);
                                    v_unused_6598_ = lean_ctor_get(v_impl_6515_, 3);
                                    lean_dec(v_unused_6598_);
                                    v_unused_6599_ = lean_ctor_get(v_impl_6515_, 2);
                                    lean_dec(v_unused_6599_);
                                    v_unused_6600_ = lean_ctor_get(v_impl_6515_, 1);
                                    lean_dec(v_unused_6600_);
                                    v_unused_6601_ = lean_ctor_get(v_impl_6515_, 0);
                                    lean_dec(v_unused_6601_);
                                    v___x_6532_ = v_impl_6515_;
                                    v_isShared_6533_ = v_isSharedCheck_6596_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_6515_);
                                    v___x_6532_ = lean_box(0);
                                    v_isShared_6533_ = v_isSharedCheck_6596_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_6602_ = lean_ctor_get(v_impl_6515_, 3);
                            lean_inc(v_l_6602_);
                            if lean_obj_tag(v_l_6602_) == 0 {
                                v_r_6603_ = lean_ctor_get(v_impl_6515_, 4);
                                v_k_6604_ = lean_ctor_get(v_impl_6515_, 1);
                                v_v_6605_ = lean_ctor_get(v_impl_6515_, 2);
                                v_isSharedCheck_6616_ = (!lean_is_exclusive(v_impl_6515_)) as u8;
                                if v_isSharedCheck_6616_ == 0 {
                                    v_unused_6617_ = lean_ctor_get(v_impl_6515_, 3);
                                    lean_dec(v_unused_6617_);
                                    v_unused_6618_ = lean_ctor_get(v_impl_6515_, 0);
                                    lean_dec(v_unused_6618_);
                                    v___x_6607_ = v_impl_6515_;
                                    v_isShared_6608_ = v_isSharedCheck_6616_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_6603_);
                                    lean_inc(v_v_6605_);
                                    lean_inc(v_k_6604_);
                                    lean_dec(v_impl_6515_);
                                    v___x_6607_ = lean_box(0);
                                    v_isShared_6608_ = v_isSharedCheck_6616_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_6619_ = lean_ctor_get(v_impl_6515_, 4);
                                lean_inc(v_r_6619_);
                                if lean_obj_tag(v_r_6619_) == 0 {
                                    v_k_6620_ = lean_ctor_get(v_impl_6515_, 1);
                                    v_v_6621_ = lean_ctor_get(v_impl_6515_, 2);
                                    v_isSharedCheck_6644_ =
                                        (!lean_is_exclusive(v_impl_6515_)) as u8;
                                    if v_isSharedCheck_6644_ == 0 {
                                        v_unused_6645_ = lean_ctor_get(v_impl_6515_, 4);
                                        lean_dec(v_unused_6645_);
                                        v_unused_6646_ = lean_ctor_get(v_impl_6515_, 3);
                                        lean_dec(v_unused_6646_);
                                        v_unused_6647_ = lean_ctor_get(v_impl_6515_, 0);
                                        lean_dec(v_unused_6647_);
                                        v___x_6623_ = v_impl_6515_;
                                        v_isShared_6624_ = v_isSharedCheck_6644_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_6621_);
                                        lean_inc(v_k_6620_);
                                        lean_dec(v_impl_6515_);
                                        v___x_6623_ = lean_box(0);
                                        v_isShared_6624_ = v_isSharedCheck_6644_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_6648_ = lean_unsigned_to_nat(2);
                                    if v_isShared_6513_ == 0 {
                                        lean_ctor_set(v___x_6512_, 4, v_r_6619_);
                                        lean_ctor_set(v___x_6512_, 3, v_impl_6515_);
                                        lean_ctor_set(v___x_6512_, 0, v___x_6648_);
                                        v___x_6650_ = v___x_6512_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6651_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6651_, 0, v___x_6648_);
                                        lean_ctor_set(v_reuseFailAlloc_6651_, 1, v_k_6507_);
                                        lean_ctor_set(v_reuseFailAlloc_6651_, 2, v_v_6508_);
                                        lean_ctor_set(v_reuseFailAlloc_6651_, 3, v_impl_6515_);
                                        lean_ctor_set(v_reuseFailAlloc_6651_, 4, v_r_6619_);
                                        v___x_6650_ = v_reuseFailAlloc_6651_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_6508_);
                        lean_dec(v_k_6507_);
                        if v_isShared_6513_ == 0 {
                            lean_ctor_set(v___x_6512_, 2, v_v_6504_);
                            lean_ctor_set(v___x_6512_, 1, v_k_6503_);
                            v___x_6653_ = v___x_6512_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_6654_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_size_6506_);
                            lean_ctor_set(v_reuseFailAlloc_6654_, 1, v_k_6503_);
                            lean_ctor_set(v_reuseFailAlloc_6654_, 2, v_v_6504_);
                            lean_ctor_set(v_reuseFailAlloc_6654_, 3, v_l_6509_);
                            lean_ctor_set(v_reuseFailAlloc_6654_, 4, v_r_6510_);
                            v___x_6653_ = v_reuseFailAlloc_6654_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_6506_);
                        v_impl_6655_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_6503_, v_v_6504_, v_r_6510_);
                        v___x_6656_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_6509_) == 0 {
                            v_size_6657_ = lean_ctor_get(v_l_6509_, 0);
                            v_size_6658_ = lean_ctor_get(v_impl_6655_, 0);
                            lean_inc(v_size_6658_);
                            v_k_6659_ = lean_ctor_get(v_impl_6655_, 1);
                            lean_inc(v_k_6659_);
                            v_v_6660_ = lean_ctor_get(v_impl_6655_, 2);
                            lean_inc(v_v_6660_);
                            v_l_6661_ = lean_ctor_get(v_impl_6655_, 3);
                            lean_inc(v_l_6661_);
                            v_r_6662_ = lean_ctor_get(v_impl_6655_, 4);
                            lean_inc(v_r_6662_);
                            v___x_6663_ = lean_unsigned_to_nat(3);
                            v___x_6664_ = lean_nat_mul(v___x_6663_, v_size_6657_);
                            v___x_6665_ = lean_nat_dec_lt(v___x_6664_, v_size_6658_);
                            lean_dec(v___x_6664_);
                            if v___x_6665_ == 0 {
                                lean_dec(v_r_6662_);
                                lean_dec(v_l_6661_);
                                lean_dec(v_v_6660_);
                                lean_dec(v_k_6659_);
                                v___x_6666_ = lean_nat_add(v___x_6656_, v_size_6657_);
                                v___x_6667_ = lean_nat_add(v___x_6666_, v_size_6658_);
                                lean_dec(v_size_6658_);
                                lean_dec(v___x_6666_);
                                if v_isShared_6513_ == 0 {
                                    lean_ctor_set(v___x_6512_, 4, v_impl_6655_);
                                    lean_ctor_set(v___x_6512_, 0, v___x_6667_);
                                    v___x_6669_ = v___x_6512_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6670_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6670_, 0, v___x_6667_);
                                    lean_ctor_set(v_reuseFailAlloc_6670_, 1, v_k_6507_);
                                    lean_ctor_set(v_reuseFailAlloc_6670_, 2, v_v_6508_);
                                    lean_ctor_set(v_reuseFailAlloc_6670_, 3, v_l_6509_);
                                    lean_ctor_set(v_reuseFailAlloc_6670_, 4, v_impl_6655_);
                                    v___x_6669_ = v_reuseFailAlloc_6670_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_6734_ = (!lean_is_exclusive(v_impl_6655_)) as u8;
                                if v_isSharedCheck_6734_ == 0 {
                                    v_unused_6735_ = lean_ctor_get(v_impl_6655_, 4);
                                    lean_dec(v_unused_6735_);
                                    v_unused_6736_ = lean_ctor_get(v_impl_6655_, 3);
                                    lean_dec(v_unused_6736_);
                                    v_unused_6737_ = lean_ctor_get(v_impl_6655_, 2);
                                    lean_dec(v_unused_6737_);
                                    v_unused_6738_ = lean_ctor_get(v_impl_6655_, 1);
                                    lean_dec(v_unused_6738_);
                                    v_unused_6739_ = lean_ctor_get(v_impl_6655_, 0);
                                    lean_dec(v_unused_6739_);
                                    v___x_6672_ = v_impl_6655_;
                                    v_isShared_6673_ = v_isSharedCheck_6734_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_6655_);
                                    v___x_6672_ = lean_box(0);
                                    v_isShared_6673_ = v_isSharedCheck_6734_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_6740_ = lean_ctor_get(v_impl_6655_, 3);
                            lean_inc(v_l_6740_);
                            if lean_obj_tag(v_l_6740_) == 0 {
                                v_r_6741_ = lean_ctor_get(v_impl_6655_, 4);
                                v_k_6742_ = lean_ctor_get(v_impl_6655_, 1);
                                v_v_6743_ = lean_ctor_get(v_impl_6655_, 2);
                                v_isSharedCheck_6766_ = (!lean_is_exclusive(v_impl_6655_)) as u8;
                                if v_isSharedCheck_6766_ == 0 {
                                    v_unused_6767_ = lean_ctor_get(v_impl_6655_, 3);
                                    lean_dec(v_unused_6767_);
                                    v_unused_6768_ = lean_ctor_get(v_impl_6655_, 0);
                                    lean_dec(v_unused_6768_);
                                    v___x_6745_ = v_impl_6655_;
                                    v_isShared_6746_ = v_isSharedCheck_6766_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_6741_);
                                    lean_inc(v_v_6743_);
                                    lean_inc(v_k_6742_);
                                    lean_dec(v_impl_6655_);
                                    v___x_6745_ = lean_box(0);
                                    v_isShared_6746_ = v_isSharedCheck_6766_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_6769_ = lean_ctor_get(v_impl_6655_, 4);
                                lean_inc(v_r_6769_);
                                if lean_obj_tag(v_r_6769_) == 0 {
                                    v_k_6770_ = lean_ctor_get(v_impl_6655_, 1);
                                    v_v_6771_ = lean_ctor_get(v_impl_6655_, 2);
                                    v_isSharedCheck_6782_ =
                                        (!lean_is_exclusive(v_impl_6655_)) as u8;
                                    if v_isSharedCheck_6782_ == 0 {
                                        v_unused_6783_ = lean_ctor_get(v_impl_6655_, 4);
                                        lean_dec(v_unused_6783_);
                                        v_unused_6784_ = lean_ctor_get(v_impl_6655_, 3);
                                        lean_dec(v_unused_6784_);
                                        v_unused_6785_ = lean_ctor_get(v_impl_6655_, 0);
                                        lean_dec(v_unused_6785_);
                                        v___x_6773_ = v_impl_6655_;
                                        v_isShared_6774_ = v_isSharedCheck_6782_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_6771_);
                                        lean_inc(v_k_6770_);
                                        lean_dec(v_impl_6655_);
                                        v___x_6773_ = lean_box(0);
                                        v_isShared_6774_ = v_isSharedCheck_6782_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_6786_ = lean_unsigned_to_nat(2);
                                    if v_isShared_6513_ == 0 {
                                        lean_ctor_set(v___x_6512_, 4, v_impl_6655_);
                                        lean_ctor_set(v___x_6512_, 3, v_r_6769_);
                                        lean_ctor_set(v___x_6512_, 0, v___x_6786_);
                                        v___x_6788_ = v___x_6512_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6789_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6789_, 0, v___x_6786_);
                                        lean_ctor_set(v_reuseFailAlloc_6789_, 1, v_k_6507_);
                                        lean_ctor_set(v_reuseFailAlloc_6789_, 2, v_v_6508_);
                                        lean_ctor_set(v_reuseFailAlloc_6789_, 3, v_r_6769_);
                                        lean_ctor_set(v_reuseFailAlloc_6789_, 4, v_impl_6655_);
                                        v___x_6788_ = v_reuseFailAlloc_6789_;
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
                return v___x_6529_;
            }
            3 => {
                v_size_6534_ = lean_ctor_get(v_l_6521_, 0);
                v_size_6535_ = lean_ctor_get(v_r_6522_, 0);
                v_k_6536_ = lean_ctor_get(v_r_6522_, 1);
                v_v_6537_ = lean_ctor_get(v_r_6522_, 2);
                v_l_6538_ = lean_ctor_get(v_r_6522_, 3);
                v_r_6539_ = lean_ctor_get(v_r_6522_, 4);
                v___x_6540_ = lean_unsigned_to_nat(2);
                v___x_6541_ = lean_nat_mul(v___x_6540_, v_size_6534_);
                v___x_6542_ = lean_nat_dec_lt(v_size_6535_, v___x_6541_);
                lean_dec(v___x_6541_);
                if v___x_6542_ == 0 {
                    lean_inc(v_r_6539_);
                    lean_inc(v_l_6538_);
                    lean_inc(v_v_6537_);
                    lean_inc(v_k_6536_);
                    v_isSharedCheck_6571_ = (!lean_is_exclusive(v_r_6522_)) as u8;
                    if v_isSharedCheck_6571_ == 0 {
                        v_unused_6572_ = lean_ctor_get(v_r_6522_, 4);
                        lean_dec(v_unused_6572_);
                        v_unused_6573_ = lean_ctor_get(v_r_6522_, 3);
                        lean_dec(v_unused_6573_);
                        v_unused_6574_ = lean_ctor_get(v_r_6522_, 2);
                        lean_dec(v_unused_6574_);
                        v_unused_6575_ = lean_ctor_get(v_r_6522_, 1);
                        lean_dec(v_unused_6575_);
                        v_unused_6576_ = lean_ctor_get(v_r_6522_, 0);
                        lean_dec(v_unused_6576_);
                        v___x_6544_ = v_r_6522_;
                        v_isShared_6545_ = v_isSharedCheck_6571_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_6522_);
                        v___x_6544_ = lean_box(0);
                        v_isShared_6545_ = v_isSharedCheck_6571_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6512_);
                    v___x_6577_ = lean_nat_add(v___x_6516_, v_size_6518_);
                    lean_dec(v_size_6518_);
                    v___x_6578_ = lean_nat_add(v___x_6577_, v_size_6517_);
                    lean_dec(v___x_6577_);
                    v___x_6579_ = lean_nat_add(v___x_6516_, v_size_6517_);
                    v___x_6580_ = lean_nat_add(v___x_6579_, v_size_6535_);
                    lean_dec(v___x_6579_);
                    lean_inc_ref(v_r_6510_);
                    if v_isShared_6533_ == 0 {
                        lean_ctor_set(v___x_6532_, 4, v_r_6510_);
                        lean_ctor_set(v___x_6532_, 3, v_r_6522_);
                        lean_ctor_set(v___x_6532_, 2, v_v_6508_);
                        lean_ctor_set(v___x_6532_, 1, v_k_6507_);
                        lean_ctor_set(v___x_6532_, 0, v___x_6580_);
                        v___x_6582_ = v___x_6532_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6595_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6595_, 0, v___x_6580_);
                        lean_ctor_set(v_reuseFailAlloc_6595_, 1, v_k_6507_);
                        lean_ctor_set(v_reuseFailAlloc_6595_, 2, v_v_6508_);
                        lean_ctor_set(v_reuseFailAlloc_6595_, 3, v_r_6522_);
                        lean_ctor_set(v_reuseFailAlloc_6595_, 4, v_r_6510_);
                        v___x_6582_ = v_reuseFailAlloc_6595_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6546_ = lean_nat_add(v___x_6516_, v_size_6518_);
                lean_dec(v_size_6518_);
                v___x_6547_ = lean_nat_add(v___x_6546_, v_size_6517_);
                lean_dec(v___x_6546_);
                v___x_6559_ = lean_nat_add(v___x_6516_, v_size_6534_);
                if lean_obj_tag(v_l_6538_) == 0 {
                    v_size_6569_ = lean_ctor_get(v_l_6538_, 0);
                    lean_inc(v_size_6569_);
                    v___y_6561_ = v_size_6569_;
                    state = 8;
                    continue;
                } else {
                    v___x_6570_ = lean_unsigned_to_nat(0);
                    v___y_6561_ = v___x_6570_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_6552_ = lean_nat_add(v___y_6550_, v___y_6551_);
                lean_dec(v___y_6551_);
                lean_dec(v___y_6550_);
                if v_isShared_6545_ == 0 {
                    lean_ctor_set(v___x_6544_, 4, v_r_6510_);
                    lean_ctor_set(v___x_6544_, 3, v_r_6539_);
                    lean_ctor_set(v___x_6544_, 2, v_v_6508_);
                    lean_ctor_set(v___x_6544_, 1, v_k_6507_);
                    lean_ctor_set(v___x_6544_, 0, v___x_6552_);
                    v___x_6554_ = v___x_6544_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6558_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 0, v___x_6552_);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 1, v_k_6507_);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 2, v_v_6508_);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 3, v_r_6539_);
                    lean_ctor_set(v_reuseFailAlloc_6558_, 4, v_r_6510_);
                    v___x_6554_ = v_reuseFailAlloc_6558_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6533_ == 0 {
                    lean_ctor_set(v___x_6532_, 4, v___x_6554_);
                    lean_ctor_set(v___x_6532_, 3, v___y_6549_);
                    lean_ctor_set(v___x_6532_, 2, v_v_6537_);
                    lean_ctor_set(v___x_6532_, 1, v_k_6536_);
                    lean_ctor_set(v___x_6532_, 0, v___x_6547_);
                    v___x_6556_ = v___x_6532_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6557_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6557_, 0, v___x_6547_);
                    lean_ctor_set(v_reuseFailAlloc_6557_, 1, v_k_6536_);
                    lean_ctor_set(v_reuseFailAlloc_6557_, 2, v_v_6537_);
                    lean_ctor_set(v_reuseFailAlloc_6557_, 3, v___y_6549_);
                    lean_ctor_set(v_reuseFailAlloc_6557_, 4, v___x_6554_);
                    v___x_6556_ = v_reuseFailAlloc_6557_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6556_;
            }
            8 => {
                v___x_6562_ = lean_nat_add(v___x_6559_, v___y_6561_);
                lean_dec(v___y_6561_);
                lean_dec(v___x_6559_);
                if v_isShared_6513_ == 0 {
                    lean_ctor_set(v___x_6512_, 4, v_l_6538_);
                    lean_ctor_set(v___x_6512_, 3, v_l_6521_);
                    lean_ctor_set(v___x_6512_, 2, v_v_6520_);
                    lean_ctor_set(v___x_6512_, 1, v_k_6519_);
                    lean_ctor_set(v___x_6512_, 0, v___x_6562_);
                    v___x_6564_ = v___x_6512_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6568_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6568_, 0, v___x_6562_);
                    lean_ctor_set(v_reuseFailAlloc_6568_, 1, v_k_6519_);
                    lean_ctor_set(v_reuseFailAlloc_6568_, 2, v_v_6520_);
                    lean_ctor_set(v_reuseFailAlloc_6568_, 3, v_l_6521_);
                    lean_ctor_set(v_reuseFailAlloc_6568_, 4, v_l_6538_);
                    v___x_6564_ = v_reuseFailAlloc_6568_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6565_ = lean_nat_add(v___x_6516_, v_size_6517_);
                if lean_obj_tag(v_r_6539_) == 0 {
                    v_size_6566_ = lean_ctor_get(v_r_6539_, 0);
                    lean_inc(v_size_6566_);
                    v___y_6549_ = v___x_6564_;
                    v___y_6550_ = v___x_6565_;
                    v___y_6551_ = v_size_6566_;
                    state = 5;
                    continue;
                } else {
                    v___x_6567_ = lean_unsigned_to_nat(0);
                    v___y_6549_ = v___x_6564_;
                    v___y_6550_ = v___x_6565_;
                    v___y_6551_ = v___x_6567_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_6589_ = (!lean_is_exclusive(v_r_6510_)) as u8;
                if v_isSharedCheck_6589_ == 0 {
                    v_unused_6590_ = lean_ctor_get(v_r_6510_, 4);
                    lean_dec(v_unused_6590_);
                    v_unused_6591_ = lean_ctor_get(v_r_6510_, 3);
                    lean_dec(v_unused_6591_);
                    v_unused_6592_ = lean_ctor_get(v_r_6510_, 2);
                    lean_dec(v_unused_6592_);
                    v_unused_6593_ = lean_ctor_get(v_r_6510_, 1);
                    lean_dec(v_unused_6593_);
                    v_unused_6594_ = lean_ctor_get(v_r_6510_, 0);
                    lean_dec(v_unused_6594_);
                    v___x_6584_ = v_r_6510_;
                    v_isShared_6585_ = v_isSharedCheck_6589_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_6510_);
                    v___x_6584_ = lean_box(0);
                    v_isShared_6585_ = v_isSharedCheck_6589_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_6585_ == 0 {
                    lean_ctor_set(v___x_6584_, 4, v___x_6582_);
                    lean_ctor_set(v___x_6584_, 3, v_l_6521_);
                    lean_ctor_set(v___x_6584_, 2, v_v_6520_);
                    lean_ctor_set(v___x_6584_, 1, v_k_6519_);
                    lean_ctor_set(v___x_6584_, 0, v___x_6578_);
                    v___x_6587_ = v___x_6584_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6588_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6588_, 0, v___x_6578_);
                    lean_ctor_set(v_reuseFailAlloc_6588_, 1, v_k_6519_);
                    lean_ctor_set(v_reuseFailAlloc_6588_, 2, v_v_6520_);
                    lean_ctor_set(v_reuseFailAlloc_6588_, 3, v_l_6521_);
                    lean_ctor_set(v_reuseFailAlloc_6588_, 4, v___x_6582_);
                    v___x_6587_ = v_reuseFailAlloc_6588_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6587_;
            }
            13 => {
                v___x_6609_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_6603_);
                if v_isShared_6608_ == 0 {
                    lean_ctor_set(v___x_6607_, 3, v_r_6603_);
                    lean_ctor_set(v___x_6607_, 2, v_v_6508_);
                    lean_ctor_set(v___x_6607_, 1, v_k_6507_);
                    lean_ctor_set(v___x_6607_, 0, v___x_6516_);
                    v___x_6611_ = v___x_6607_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6615_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6615_, 0, v___x_6516_);
                    lean_ctor_set(v_reuseFailAlloc_6615_, 1, v_k_6507_);
                    lean_ctor_set(v_reuseFailAlloc_6615_, 2, v_v_6508_);
                    lean_ctor_set(v_reuseFailAlloc_6615_, 3, v_r_6603_);
                    lean_ctor_set(v_reuseFailAlloc_6615_, 4, v_r_6603_);
                    v___x_6611_ = v_reuseFailAlloc_6615_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_6513_ == 0 {
                    lean_ctor_set(v___x_6512_, 4, v___x_6611_);
                    lean_ctor_set(v___x_6512_, 3, v_l_6602_);
                    lean_ctor_set(v___x_6512_, 2, v_v_6605_);
                    lean_ctor_set(v___x_6512_, 1, v_k_6604_);
                    lean_ctor_set(v___x_6512_, 0, v___x_6609_);
                    v___x_6613_ = v___x_6512_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6614_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6614_, 0, v___x_6609_);
                    lean_ctor_set(v_reuseFailAlloc_6614_, 1, v_k_6604_);
                    lean_ctor_set(v_reuseFailAlloc_6614_, 2, v_v_6605_);
                    lean_ctor_set(v_reuseFailAlloc_6614_, 3, v_l_6602_);
                    lean_ctor_set(v_reuseFailAlloc_6614_, 4, v___x_6611_);
                    v___x_6613_ = v_reuseFailAlloc_6614_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6613_;
            }
            16 => {
                v_k_6625_ = lean_ctor_get(v_r_6619_, 1);
                v_v_6626_ = lean_ctor_get(v_r_6619_, 2);
                v_isSharedCheck_6640_ = (!lean_is_exclusive(v_r_6619_)) as u8;
                if v_isSharedCheck_6640_ == 0 {
                    v_unused_6641_ = lean_ctor_get(v_r_6619_, 4);
                    lean_dec(v_unused_6641_);
                    v_unused_6642_ = lean_ctor_get(v_r_6619_, 3);
                    lean_dec(v_unused_6642_);
                    v_unused_6643_ = lean_ctor_get(v_r_6619_, 0);
                    lean_dec(v_unused_6643_);
                    v___x_6628_ = v_r_6619_;
                    v_isShared_6629_ = v_isSharedCheck_6640_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_6626_);
                    lean_inc(v_k_6625_);
                    lean_dec(v_r_6619_);
                    v___x_6628_ = lean_box(0);
                    v_isShared_6629_ = v_isSharedCheck_6640_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_6630_ = lean_unsigned_to_nat(3);
                if v_isShared_6629_ == 0 {
                    lean_ctor_set(v___x_6628_, 4, v_l_6602_);
                    lean_ctor_set(v___x_6628_, 3, v_l_6602_);
                    lean_ctor_set(v___x_6628_, 2, v_v_6621_);
                    lean_ctor_set(v___x_6628_, 1, v_k_6620_);
                    lean_ctor_set(v___x_6628_, 0, v___x_6516_);
                    v___x_6632_ = v___x_6628_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6639_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6639_, 0, v___x_6516_);
                    lean_ctor_set(v_reuseFailAlloc_6639_, 1, v_k_6620_);
                    lean_ctor_set(v_reuseFailAlloc_6639_, 2, v_v_6621_);
                    lean_ctor_set(v_reuseFailAlloc_6639_, 3, v_l_6602_);
                    lean_ctor_set(v_reuseFailAlloc_6639_, 4, v_l_6602_);
                    v___x_6632_ = v_reuseFailAlloc_6639_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_6624_ == 0 {
                    lean_ctor_set(v___x_6623_, 4, v_l_6602_);
                    lean_ctor_set(v___x_6623_, 2, v_v_6508_);
                    lean_ctor_set(v___x_6623_, 1, v_k_6507_);
                    lean_ctor_set(v___x_6623_, 0, v___x_6516_);
                    v___x_6634_ = v___x_6623_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6638_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6638_, 0, v___x_6516_);
                    lean_ctor_set(v_reuseFailAlloc_6638_, 1, v_k_6507_);
                    lean_ctor_set(v_reuseFailAlloc_6638_, 2, v_v_6508_);
                    lean_ctor_set(v_reuseFailAlloc_6638_, 3, v_l_6602_);
                    lean_ctor_set(v_reuseFailAlloc_6638_, 4, v_l_6602_);
                    v___x_6634_ = v_reuseFailAlloc_6638_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_6513_ == 0 {
                    lean_ctor_set(v___x_6512_, 4, v___x_6634_);
                    lean_ctor_set(v___x_6512_, 3, v___x_6632_);
                    lean_ctor_set(v___x_6512_, 2, v_v_6626_);
                    lean_ctor_set(v___x_6512_, 1, v_k_6625_);
                    lean_ctor_set(v___x_6512_, 0, v___x_6630_);
                    v___x_6636_ = v___x_6512_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6637_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6637_, 0, v___x_6630_);
                    lean_ctor_set(v_reuseFailAlloc_6637_, 1, v_k_6625_);
                    lean_ctor_set(v_reuseFailAlloc_6637_, 2, v_v_6626_);
                    lean_ctor_set(v_reuseFailAlloc_6637_, 3, v___x_6632_);
                    lean_ctor_set(v_reuseFailAlloc_6637_, 4, v___x_6634_);
                    v___x_6636_ = v_reuseFailAlloc_6637_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6636_;
            }
            21 => {
                return v___x_6650_;
            }
            22 => {
                return v___x_6653_;
            }
            23 => {
                return v___x_6669_;
            }
            24 => {
                v_size_6674_ = lean_ctor_get(v_l_6661_, 0);
                v_k_6675_ = lean_ctor_get(v_l_6661_, 1);
                v_v_6676_ = lean_ctor_get(v_l_6661_, 2);
                v_l_6677_ = lean_ctor_get(v_l_6661_, 3);
                v_r_6678_ = lean_ctor_get(v_l_6661_, 4);
                v_size_6679_ = lean_ctor_get(v_r_6662_, 0);
                v___x_6680_ = lean_unsigned_to_nat(2);
                v___x_6681_ = lean_nat_mul(v___x_6680_, v_size_6679_);
                v___x_6682_ = lean_nat_dec_lt(v_size_6674_, v___x_6681_);
                lean_dec(v___x_6681_);
                if v___x_6682_ == 0 {
                    lean_inc(v_r_6678_);
                    lean_inc(v_l_6677_);
                    lean_inc(v_v_6676_);
                    lean_inc(v_k_6675_);
                    v_isSharedCheck_6710_ = (!lean_is_exclusive(v_l_6661_)) as u8;
                    if v_isSharedCheck_6710_ == 0 {
                        v_unused_6711_ = lean_ctor_get(v_l_6661_, 4);
                        lean_dec(v_unused_6711_);
                        v_unused_6712_ = lean_ctor_get(v_l_6661_, 3);
                        lean_dec(v_unused_6712_);
                        v_unused_6713_ = lean_ctor_get(v_l_6661_, 2);
                        lean_dec(v_unused_6713_);
                        v_unused_6714_ = lean_ctor_get(v_l_6661_, 1);
                        lean_dec(v_unused_6714_);
                        v_unused_6715_ = lean_ctor_get(v_l_6661_, 0);
                        lean_dec(v_unused_6715_);
                        v___x_6684_ = v_l_6661_;
                        v_isShared_6685_ = v_isSharedCheck_6710_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_6661_);
                        v___x_6684_ = lean_box(0);
                        v_isShared_6685_ = v_isSharedCheck_6710_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6512_);
                    v___x_6716_ = lean_nat_add(v___x_6656_, v_size_6657_);
                    v___x_6717_ = lean_nat_add(v___x_6716_, v_size_6658_);
                    lean_dec(v_size_6658_);
                    v___x_6718_ = lean_nat_add(v___x_6716_, v_size_6674_);
                    lean_dec(v___x_6716_);
                    lean_inc_ref(v_l_6509_);
                    if v_isShared_6673_ == 0 {
                        lean_ctor_set(v___x_6672_, 4, v_l_6661_);
                        lean_ctor_set(v___x_6672_, 3, v_l_6509_);
                        lean_ctor_set(v___x_6672_, 2, v_v_6508_);
                        lean_ctor_set(v___x_6672_, 1, v_k_6507_);
                        lean_ctor_set(v___x_6672_, 0, v___x_6718_);
                        v___x_6720_ = v___x_6672_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_6733_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6733_, 0, v___x_6718_);
                        lean_ctor_set(v_reuseFailAlloc_6733_, 1, v_k_6507_);
                        lean_ctor_set(v_reuseFailAlloc_6733_, 2, v_v_6508_);
                        lean_ctor_set(v_reuseFailAlloc_6733_, 3, v_l_6509_);
                        lean_ctor_set(v_reuseFailAlloc_6733_, 4, v_l_6661_);
                        v___x_6720_ = v_reuseFailAlloc_6733_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_6686_ = lean_nat_add(v___x_6656_, v_size_6657_);
                v___x_6687_ = lean_nat_add(v___x_6686_, v_size_6658_);
                lean_dec(v_size_6658_);
                if lean_obj_tag(v_l_6677_) == 0 {
                    v_size_6708_ = lean_ctor_get(v_l_6677_, 0);
                    lean_inc(v_size_6708_);
                    v___y_6700_ = v_size_6708_;
                    state = 29;
                    continue;
                } else {
                    v___x_6709_ = lean_unsigned_to_nat(0);
                    v___y_6700_ = v___x_6709_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_6692_ = lean_nat_add(v___y_6689_, v___y_6691_);
                lean_dec(v___y_6691_);
                lean_dec(v___y_6689_);
                if v_isShared_6685_ == 0 {
                    lean_ctor_set(v___x_6684_, 4, v_r_6662_);
                    lean_ctor_set(v___x_6684_, 3, v_r_6678_);
                    lean_ctor_set(v___x_6684_, 2, v_v_6660_);
                    lean_ctor_set(v___x_6684_, 1, v_k_6659_);
                    lean_ctor_set(v___x_6684_, 0, v___x_6692_);
                    v___x_6694_ = v___x_6684_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6698_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6698_, 0, v___x_6692_);
                    lean_ctor_set(v_reuseFailAlloc_6698_, 1, v_k_6659_);
                    lean_ctor_set(v_reuseFailAlloc_6698_, 2, v_v_6660_);
                    lean_ctor_set(v_reuseFailAlloc_6698_, 3, v_r_6678_);
                    lean_ctor_set(v_reuseFailAlloc_6698_, 4, v_r_6662_);
                    v___x_6694_ = v_reuseFailAlloc_6698_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_6673_ == 0 {
                    lean_ctor_set(v___x_6672_, 4, v___x_6694_);
                    lean_ctor_set(v___x_6672_, 3, v___y_6690_);
                    lean_ctor_set(v___x_6672_, 2, v_v_6676_);
                    lean_ctor_set(v___x_6672_, 1, v_k_6675_);
                    lean_ctor_set(v___x_6672_, 0, v___x_6687_);
                    v___x_6696_ = v___x_6672_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6697_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6697_, 0, v___x_6687_);
                    lean_ctor_set(v_reuseFailAlloc_6697_, 1, v_k_6675_);
                    lean_ctor_set(v_reuseFailAlloc_6697_, 2, v_v_6676_);
                    lean_ctor_set(v_reuseFailAlloc_6697_, 3, v___y_6690_);
                    lean_ctor_set(v_reuseFailAlloc_6697_, 4, v___x_6694_);
                    v___x_6696_ = v_reuseFailAlloc_6697_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6696_;
            }
            29 => {
                v___x_6701_ = lean_nat_add(v___x_6686_, v___y_6700_);
                lean_dec(v___y_6700_);
                lean_dec(v___x_6686_);
                if v_isShared_6513_ == 0 {
                    lean_ctor_set(v___x_6512_, 4, v_l_6677_);
                    lean_ctor_set(v___x_6512_, 0, v___x_6701_);
                    v___x_6703_ = v___x_6512_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6707_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6707_, 0, v___x_6701_);
                    lean_ctor_set(v_reuseFailAlloc_6707_, 1, v_k_6507_);
                    lean_ctor_set(v_reuseFailAlloc_6707_, 2, v_v_6508_);
                    lean_ctor_set(v_reuseFailAlloc_6707_, 3, v_l_6509_);
                    lean_ctor_set(v_reuseFailAlloc_6707_, 4, v_l_6677_);
                    v___x_6703_ = v_reuseFailAlloc_6707_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_6704_ = lean_nat_add(v___x_6656_, v_size_6679_);
                if lean_obj_tag(v_r_6678_) == 0 {
                    v_size_6705_ = lean_ctor_get(v_r_6678_, 0);
                    lean_inc(v_size_6705_);
                    v___y_6689_ = v___x_6704_;
                    v___y_6690_ = v___x_6703_;
                    v___y_6691_ = v_size_6705_;
                    state = 26;
                    continue;
                } else {
                    v___x_6706_ = lean_unsigned_to_nat(0);
                    v___y_6689_ = v___x_6704_;
                    v___y_6690_ = v___x_6703_;
                    v___y_6691_ = v___x_6706_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_6727_ = (!lean_is_exclusive(v_l_6509_)) as u8;
                if v_isSharedCheck_6727_ == 0 {
                    v_unused_6728_ = lean_ctor_get(v_l_6509_, 4);
                    lean_dec(v_unused_6728_);
                    v_unused_6729_ = lean_ctor_get(v_l_6509_, 3);
                    lean_dec(v_unused_6729_);
                    v_unused_6730_ = lean_ctor_get(v_l_6509_, 2);
                    lean_dec(v_unused_6730_);
                    v_unused_6731_ = lean_ctor_get(v_l_6509_, 1);
                    lean_dec(v_unused_6731_);
                    v_unused_6732_ = lean_ctor_get(v_l_6509_, 0);
                    lean_dec(v_unused_6732_);
                    v___x_6722_ = v_l_6509_;
                    v_isShared_6723_ = v_isSharedCheck_6727_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_6509_);
                    v___x_6722_ = lean_box(0);
                    v_isShared_6723_ = v_isSharedCheck_6727_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_6723_ == 0 {
                    lean_ctor_set(v___x_6722_, 4, v_r_6662_);
                    lean_ctor_set(v___x_6722_, 3, v___x_6720_);
                    lean_ctor_set(v___x_6722_, 2, v_v_6660_);
                    lean_ctor_set(v___x_6722_, 1, v_k_6659_);
                    lean_ctor_set(v___x_6722_, 0, v___x_6717_);
                    v___x_6725_ = v___x_6722_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6726_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6726_, 0, v___x_6717_);
                    lean_ctor_set(v_reuseFailAlloc_6726_, 1, v_k_6659_);
                    lean_ctor_set(v_reuseFailAlloc_6726_, 2, v_v_6660_);
                    lean_ctor_set(v_reuseFailAlloc_6726_, 3, v___x_6720_);
                    lean_ctor_set(v_reuseFailAlloc_6726_, 4, v_r_6662_);
                    v___x_6725_ = v_reuseFailAlloc_6726_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6725_;
            }
            34 => {
                v_k_6747_ = lean_ctor_get(v_l_6740_, 1);
                v_v_6748_ = lean_ctor_get(v_l_6740_, 2);
                v_isSharedCheck_6762_ = (!lean_is_exclusive(v_l_6740_)) as u8;
                if v_isSharedCheck_6762_ == 0 {
                    v_unused_6763_ = lean_ctor_get(v_l_6740_, 4);
                    lean_dec(v_unused_6763_);
                    v_unused_6764_ = lean_ctor_get(v_l_6740_, 3);
                    lean_dec(v_unused_6764_);
                    v_unused_6765_ = lean_ctor_get(v_l_6740_, 0);
                    lean_dec(v_unused_6765_);
                    v___x_6750_ = v_l_6740_;
                    v_isShared_6751_ = v_isSharedCheck_6762_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_6748_);
                    lean_inc(v_k_6747_);
                    lean_dec(v_l_6740_);
                    v___x_6750_ = lean_box(0);
                    v_isShared_6751_ = v_isSharedCheck_6762_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_6752_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_6741_, 2);
                if v_isShared_6751_ == 0 {
                    lean_ctor_set(v___x_6750_, 4, v_r_6741_);
                    lean_ctor_set(v___x_6750_, 3, v_r_6741_);
                    lean_ctor_set(v___x_6750_, 2, v_v_6508_);
                    lean_ctor_set(v___x_6750_, 1, v_k_6507_);
                    lean_ctor_set(v___x_6750_, 0, v___x_6656_);
                    v___x_6754_ = v___x_6750_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6761_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6761_, 0, v___x_6656_);
                    lean_ctor_set(v_reuseFailAlloc_6761_, 1, v_k_6507_);
                    lean_ctor_set(v_reuseFailAlloc_6761_, 2, v_v_6508_);
                    lean_ctor_set(v_reuseFailAlloc_6761_, 3, v_r_6741_);
                    lean_ctor_set(v_reuseFailAlloc_6761_, 4, v_r_6741_);
                    v___x_6754_ = v_reuseFailAlloc_6761_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_6741_);
                if v_isShared_6746_ == 0 {
                    lean_ctor_set(v___x_6745_, 3, v_r_6741_);
                    lean_ctor_set(v___x_6745_, 0, v___x_6656_);
                    v___x_6756_ = v___x_6745_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6760_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6760_, 0, v___x_6656_);
                    lean_ctor_set(v_reuseFailAlloc_6760_, 1, v_k_6742_);
                    lean_ctor_set(v_reuseFailAlloc_6760_, 2, v_v_6743_);
                    lean_ctor_set(v_reuseFailAlloc_6760_, 3, v_r_6741_);
                    lean_ctor_set(v_reuseFailAlloc_6760_, 4, v_r_6741_);
                    v___x_6756_ = v_reuseFailAlloc_6760_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_6513_ == 0 {
                    lean_ctor_set(v___x_6512_, 4, v___x_6756_);
                    lean_ctor_set(v___x_6512_, 3, v___x_6754_);
                    lean_ctor_set(v___x_6512_, 2, v_v_6748_);
                    lean_ctor_set(v___x_6512_, 1, v_k_6747_);
                    lean_ctor_set(v___x_6512_, 0, v___x_6752_);
                    v___x_6758_ = v___x_6512_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_6759_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6759_, 0, v___x_6752_);
                    lean_ctor_set(v_reuseFailAlloc_6759_, 1, v_k_6747_);
                    lean_ctor_set(v_reuseFailAlloc_6759_, 2, v_v_6748_);
                    lean_ctor_set(v_reuseFailAlloc_6759_, 3, v___x_6754_);
                    lean_ctor_set(v_reuseFailAlloc_6759_, 4, v___x_6756_);
                    v___x_6758_ = v_reuseFailAlloc_6759_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_6758_;
            }
            39 => {
                v___x_6775_ = lean_unsigned_to_nat(3);
                if v_isShared_6774_ == 0 {
                    lean_ctor_set(v___x_6773_, 4, v_l_6740_);
                    lean_ctor_set(v___x_6773_, 2, v_v_6508_);
                    lean_ctor_set(v___x_6773_, 1, v_k_6507_);
                    lean_ctor_set(v___x_6773_, 0, v___x_6656_);
                    v___x_6777_ = v___x_6773_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_6781_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6781_, 0, v___x_6656_);
                    lean_ctor_set(v_reuseFailAlloc_6781_, 1, v_k_6507_);
                    lean_ctor_set(v_reuseFailAlloc_6781_, 2, v_v_6508_);
                    lean_ctor_set(v_reuseFailAlloc_6781_, 3, v_l_6740_);
                    lean_ctor_set(v_reuseFailAlloc_6781_, 4, v_l_6740_);
                    v___x_6777_ = v_reuseFailAlloc_6781_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_6513_ == 0 {
                    lean_ctor_set(v___x_6512_, 4, v_r_6769_);
                    lean_ctor_set(v___x_6512_, 3, v___x_6777_);
                    lean_ctor_set(v___x_6512_, 2, v_v_6771_);
                    lean_ctor_set(v___x_6512_, 1, v_k_6770_);
                    lean_ctor_set(v___x_6512_, 0, v___x_6775_);
                    v___x_6779_ = v___x_6512_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6780_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6780_, 0, v___x_6775_);
                    lean_ctor_set(v_reuseFailAlloc_6780_, 1, v_k_6770_);
                    lean_ctor_set(v_reuseFailAlloc_6780_, 2, v_v_6771_);
                    lean_ctor_set(v_reuseFailAlloc_6780_, 3, v___x_6777_);
                    lean_ctor_set(v_reuseFailAlloc_6780_, 4, v_r_6769_);
                    v___x_6779_ = v_reuseFailAlloc_6780_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6779_;
            }
            42 => {
                return v___x_6788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__0() -> *mut LeanObject {
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    v___x_6793_ = lean_box(1);
    v___x_6794_ = l_Lake_Package_depsFacetConfig;
    v___x_6795_ = l_Lake_Package_depsFacet;
    v___x_6796_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6795_,
            v___x_6794_,
            v___x_6793_,
        );
    return v___x_6796_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__1() -> *mut LeanObject {
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    v___x_6797_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__0_once),
        _init_l_Lake_Package_initFacetConfigs___closed__0,
    );
    v___x_6798_ = l_Lake_Package_transDepsFacetConfig;
    v___x_6799_ = l_Lake_Package_transDepsFacet;
    v___x_6800_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6799_,
            v___x_6798_,
            v___x_6797_,
        );
    return v___x_6800_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__2() -> *mut LeanObject {
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    v___x_6801_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__1_once),
        _init_l_Lake_Package_initFacetConfigs___closed__1,
    );
    v___x_6802_ = l_Lake_Package_extraDepFacetConfig;
    v___x_6803_ = l_Lake_Package_extraDepFacet;
    v___x_6804_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6803_,
            v___x_6802_,
            v___x_6801_,
        );
    return v___x_6804_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__3() -> *mut LeanObject {
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    v___x_6805_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__2_once),
        _init_l_Lake_Package_initFacetConfigs___closed__2,
    );
    v___x_6806_ = l_Lake_Package_optBuildCacheFacetConfig;
    v___x_6807_ = l_Lake_Package_optBuildCacheFacet;
    v___x_6808_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6807_,
            v___x_6806_,
            v___x_6805_,
        );
    return v___x_6808_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__4() -> *mut LeanObject {
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
    v___x_6809_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__3_once),
        _init_l_Lake_Package_initFacetConfigs___closed__3,
    );
    v___x_6810_ = l_Lake_Package_buildCacheFacetConfig;
    v___x_6811_ = l_Lake_Package_buildCacheFacet;
    v___x_6812_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6811_,
            v___x_6810_,
            v___x_6809_,
        );
    return v___x_6812_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__5() -> *mut LeanObject {
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    v___x_6813_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__4_once),
        _init_l_Lake_Package_initFacetConfigs___closed__4,
    );
    v___x_6814_ = l_Lake_Package_optBarrelFacetConfig;
    v___x_6815_ = l_Lake_Package_optReservoirBarrelFacet;
    v___x_6816_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6815_,
            v___x_6814_,
            v___x_6813_,
        );
    return v___x_6816_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__6() -> *mut LeanObject {
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    v___x_6817_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__5_once),
        _init_l_Lake_Package_initFacetConfigs___closed__5,
    );
    v___x_6818_ = l_Lake_Package_barrelFacetConfig;
    v___x_6819_ = l_Lake_Package_reservoirBarrelFacet;
    v___x_6820_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6819_,
            v___x_6818_,
            v___x_6817_,
        );
    return v___x_6820_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__7() -> *mut LeanObject {
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    v___x_6821_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__6_once),
        _init_l_Lake_Package_initFacetConfigs___closed__6,
    );
    v___x_6822_ = l_Lake_Package_optGitHubReleaseFacetConfig;
    v___x_6823_ = l_Lake_Package_optGitHubReleaseFacet;
    v___x_6824_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6823_,
            v___x_6822_,
            v___x_6821_,
        );
    return v___x_6824_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs___closed__8() -> *mut LeanObject {
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    v___x_6825_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__7_once),
        _init_l_Lake_Package_initFacetConfigs___closed__7,
    );
    v___x_6826_ = l_Lake_Package_gitHubReleaseFacetConfig;
    v___x_6827_ = l_Lake_Package_gitHubReleaseFacet;
    v___x_6828_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v___x_6827_,
            v___x_6826_,
            v___x_6825_,
        );
    return v___x_6828_;
}
pub unsafe fn _init_l_Lake_Package_initFacetConfigs() -> *mut LeanObject {
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    v___x_6829_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Package_initFacetConfigs___closed__8_once),
        _init_l_Lake_Package_initFacetConfigs___closed__8,
    );
    return v___x_6829_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(
    mut v_00_u03b2_6830_: *mut LeanObject,
    mut v_k_6831_: *mut LeanObject,
    mut v_v_6832_: *mut LeanObject,
    mut v_t_6833_: *mut LeanObject,
    mut v_hl_6834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    v___x_6835_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(
            v_k_6831_, v_v_6832_, v_t_6833_,
        );
    return v___x_6835_;
}
pub unsafe fn _init_l_Lake_initPackageFacetConfigs() -> *mut LeanObject {
    let mut v___x_6836_: *mut LeanObject = core::ptr::null_mut();
    v___x_6836_ = l_Lake_Package_initFacetConfigs;
    return v___x_6836_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Package(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lake_Build_Job_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Url(builtin);
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
    res = runtime_initialize_Lake_Reservoir(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
    lean_mark_persistent(l_Lake_Package_depsFacetConfig);
    l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2 = _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2();
    lean_mark_persistent(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2);
    l_Lake_Package_transDepsFacetConfig = _init_l_Lake_Package_transDepsFacetConfig();
    lean_mark_persistent(l_Lake_Package_transDepsFacetConfig);
    l_Lake_Package_optBuildCacheFacetConfig = _init_l_Lake_Package_optBuildCacheFacetConfig();
    lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig);
    l_Lake_Package_extraDepFacetConfig = _init_l_Lake_Package_extraDepFacetConfig();
    lean_mark_persistent(l_Lake_Package_extraDepFacetConfig);
    l_Lake_Package_buildCacheFacetConfig = _init_l_Lake_Package_buildCacheFacetConfig();
    lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig);
    l_Lake_Package_optBarrelFacetConfig = _init_l_Lake_Package_optBarrelFacetConfig();
    lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig);
    l_Lake_Package_barrelFacetConfig = _init_l_Lake_Package_barrelFacetConfig();
    lean_mark_persistent(l_Lake_Package_barrelFacetConfig);
    l_Lake_Package_optGitHubReleaseFacetConfig = _init_l_Lake_Package_optGitHubReleaseFacetConfig();
    lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig);
    l_Lake_Package_gitHubReleaseFacetConfig = _init_l_Lake_Package_gitHubReleaseFacetConfig();
    lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig);
    l_Lake_Package_initFacetConfigs = _init_l_Lake_Package_initFacetConfigs();
    lean_mark_persistent(l_Lake_Package_initFacetConfigs);
    l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
    lean_mark_persistent(l_Lake_initPackageFacetConfigs);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Package(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Package(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lake_Build_Job_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Url(builtin);
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
    res = initialize_Lake_Reservoir(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Package(builtin);
}
