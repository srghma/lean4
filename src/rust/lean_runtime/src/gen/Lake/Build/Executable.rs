// Lean compiler output
// Module: Lake.Build.Executable
// Imports: Lake.Config.FacetConfig Lake.Build.Job.Register Lake.Build.Target.Fetch Lake.Build.Common Lake.Build.Infos
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_exeExtension, l_System_FilePath_normalize,
};
use crate::r#gen::Init::System::Platform::l_System_Platform_isWindows;
use crate::r#gen::Lake::Build::Common::{
    initialize_Lake_Build_Common, l_Lake_buildLeanExe, runtime_initialize_Lake_Build_Common,
};
use crate::r#gen::Lake::Build::Data::{l_Lake_instDataKindDynlib, l_Lake_instDataKindFilePath};
use crate::r#gen::Lake::Build::Facets::{
    l_Lake_ExternLib_staticFacet, l_Lake_LeanExe_defaultFacet, l_Lake_LeanExe_exeFacet,
};
use crate::r#gen::Lake::Build::Fetch::l_Lake_ModuleFacet_fetch___redArg;
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, l_Lake_Module_transImportsFacet, l_Lake_Package_transDepsFacet,
    runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_Job_toOpaque___redArg;
use crate::r#gen::Lake::Build::Job::Monad::l_Lake_Job_await___redArg;
use crate::r#gen::Lake::Build::Job::Register::{
    initialize_Lake_Build_Job_Register, l_Lake_Job_renew___redArg, l_Lake_ensureJob___redArg,
    runtime_initialize_Lake_Build_Job_Register,
};
use crate::r#gen::Lake::Build::Key::l_Lake_PartialBuildKey_toString;
use crate::r#gen::Lake::Build::Target::Fetch::{
    initialize_Lake_Build_Target_Fetch,
    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux,
    runtime_initialize_Lake_Build_Target_Fetch,
};
use crate::r#gen::Lake::Build::Trace::l_Lake_BuildTrace_nil;
use crate::r#gen::Lake::Config::FacetConfig::{
    initialize_Lake_Config_FacetConfig, runtime_initialize_Lake_Config_FacetConfig,
};
use crate::r#gen::Lake::Config::Kinds::{
    l_Lake_ExternLib_keyword, l_Lake_LeanExe_keyword, l_Lake_Module_keyword, l_Lake_Package_keyword,
};
use crate::r#gen::Lake::Config::LeanExe::{
    l_Lake_LeanExe_linkArgs, l_Lake_LeanExeConfig_toLeanLibConfig___redArg,
};
use crate::r#gen::Lake::Util::FilePath::{l_Lake_joinRelative, l_Lake_mkRelPathString};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::lean_imports_rs::Init::Core::lean_strict_and;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
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
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_wait;
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [39, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [39, 44, 32, 103, 111, 116, 32, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [117, 110, 107, 110, 111, 119, 110, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0: u64 = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 110, 105, 108, 62, 0]};
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [98, 97, 100, 32, 105, 109, 112, 111, 114, 116, 115, 32, 40, 115, 101, 101, 32, 116, 104, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [39, 32, 106, 111, 98, 32, 102, 111, 114, 32, 100, 101, 116, 97, 105, 108, 115, 41, 0]};
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0_value:
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
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [58, 101, 120, 101, 0],
};
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut crate::leanh::LeanObject)],
};
pub static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExe_exeFacetConfig___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExe_exeFacetConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_exeFacetConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExe_exeFacetConfig___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExe_exeFacetConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_exeFacetConfig___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExe_exeFacetConfig___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExe_exeFacetConfig___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExe_exeFacetConfig: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExe_defaultFacetConfig___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExe_defaultFacetConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_defaultFacetConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExe_defaultFacetConfig___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExe_defaultFacetConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExe_defaultFacetConfig: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanExe_initFacetConfigs___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExe_initFacetConfigs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanExe_initFacetConfigs___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExe_initFacetConfigs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExe_initFacetConfigs: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1534_: u8 = 0;
    let mut v_name_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = 1;
    v_name_1535_ = l_Lake_instDataKindDynlib;
    v___x_1536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_1535_,
        v___x_1534_,
    );
    return v___x_1536_;
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(
    mut v_defaultPkg_1540_: *mut crate::leanh::LeanObject,
    mut v_self_1541_: *mut crate::leanh::LeanObject,
    mut v_a_1542_: *mut crate::leanh::LeanObject,
    mut v_a_1543_: *mut crate::leanh::LeanObject,
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v_a_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v_kind_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_unused_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v_unused_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1599_: u8 = 0;
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1549_ = 1;
                crate::leanh::lean_inc_ref_n(v_self_1541_, 2);
                v___x_1550_ =
                    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
                        v_defaultPkg_1540_,
                        v_self_1541_,
                        v_self_1541_,
                        v___x_1549_,
                        v_a_1542_,
                        v_a_1543_,
                        v_a_1544_,
                        v_a_1545_,
                        v_a_1546_,
                        v_a_1547_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1550_) == 0 {
                    v_a_1551_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                    crate::leanh::lean_inc(v_a_1551_);
                    v_snd_1552_ = crate::leanh::lean_ctor_get(v_a_1551_, 1);
                    v_isSharedCheck_1593_ = (!crate::leanh::lean_is_exclusive(v_a_1551_)) as u8;
                    if v_isSharedCheck_1593_ == 0 {
                        v_unused_1594_ = crate::leanh::lean_ctor_get(v_a_1551_, 0);
                        crate::leanh::lean_dec(v_unused_1594_);
                        v___x_1554_ = v_a_1551_;
                        v_isShared_1555_ = v_isSharedCheck_1593_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1552_);
                        crate::leanh::lean_dec(v_a_1551_);
                        v___x_1554_ = crate::leanh::lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1593_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_self_1541_);
                    v_a_1595_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                    v_a_1596_ = crate::leanh::lean_ctor_get(v___x_1550_, 1);
                    v_isSharedCheck_1603_ = (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1598_ = v___x_1550_;
                        v_isShared_1599_ = v_isSharedCheck_1603_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1596_);
                        crate::leanh::lean_inc(v_a_1595_);
                        crate::leanh::lean_dec(v___x_1550_);
                        v___x_1598_ = crate::leanh::lean_box(0);
                        v_isShared_1599_ = v_isSharedCheck_1603_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1556_ = crate::leanh::lean_ctor_get(v___x_1550_, 1);
                v_isSharedCheck_1591_ = (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                if v_isSharedCheck_1591_ == 0 {
                    v_unused_1592_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                    crate::leanh::lean_dec(v_unused_1592_);
                    v___x_1558_ = v___x_1550_;
                    v_isShared_1559_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1556_);
                    crate::leanh::lean_dec(v___x_1550_);
                    v___x_1558_ = crate::leanh::lean_box(0);
                    v_isShared_1559_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_kind_1560_ = crate::leanh::lean_ctor_get(v_snd_1552_, 1);
                v_name_1561_ = l_Lake_instDataKindDynlib;
                v___x_1581_ = lean_name_eq(v_kind_1560_, v_name_1561_);
                if v___x_1581_ == 0 {
                    crate::leanh::lean_inc(v_kind_1560_);
                    crate::leanh::lean_del_object(v___x_1554_);
                    crate::leanh::lean_dec(v_snd_1552_);
                    v___x_1582_ = l_Lean_Name_isAnonymous(v_kind_1560_);
                    if v___x_1582_ == 0 {
                        v___x_1583_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4;
                        v___x_1584_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_1560_,
                                v___x_1549_,
                            );
                        v___x_1585_ = lean_string_append(v___x_1583_, v___x_1584_);
                        crate::leanh::lean_dec_ref(v___x_1584_);
                        v___x_1586_ = lean_string_append(v___x_1585_, v___x_1583_);
                        v___y_1563_ = v___x_1586_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_kind_1560_);
                        v___x_1587_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5;
                        v___y_1563_ = v___x_1587_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1558_);
                    crate::leanh::lean_dec_ref(v_self_1541_);
                    if v_isShared_1555_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1554_, 1, v_a_1556_);
                        crate::leanh::lean_ctor_set(v___x_1554_, 0, v_snd_1552_);
                        v___x_1589_ = v___x_1554_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_snd_1552_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_a_1556_);
                        v___x_1589_ = v_reuseFailAlloc_1590_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1564_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0;
                v___x_1565_ = l_Lake_PartialBuildKey_toString(v_self_1541_);
                v___x_1566_ = lean_string_append(v___x_1564_, v___x_1565_);
                crate::leanh::lean_dec_ref(v___x_1565_);
                v___x_1567_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1;
                v___x_1568_ = lean_string_append(v___x_1566_, v___x_1567_);
                v___x_1569_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2_once), _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2);
                v___x_1570_ = lean_string_append(v___x_1568_, v___x_1569_);
                v___x_1571_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3;
                v___x_1572_ = lean_string_append(v___x_1570_, v___x_1571_);
                v___x_1573_ = lean_string_append(v___x_1572_, v___y_1563_);
                crate::leanh::lean_dec_ref(v___y_1563_);
                v___x_1574_ = 3;
                v___x_1575_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1573_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1575_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1574_,
                );
                v___x_1576_ = lean_array_get_size(v_a_1556_);
                v___x_1577_ = lean_array_push(v_a_1556_, v___x_1575_);
                if v_isShared_1559_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1558_, 1);
                    crate::leanh::lean_ctor_set(v___x_1558_, 1, v___x_1577_);
                    crate::leanh::lean_ctor_set(v___x_1558_, 0, v___x_1576_);
                    v___x_1579_ = v___x_1558_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 1, v___x_1577_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1579_;
            }
            5 => {
                return v___x_1589_;
            }
            6 => {
                if v_isShared_1599_ == 0 {
                    v___x_1601_ = v___x_1598_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_a_1596_);
                    v___x_1601_ = v_reuseFailAlloc_1602_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___boxed(
    mut v_defaultPkg_1604_: *mut crate::leanh::LeanObject,
    mut v_self_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
    mut v_a_1610_: *mut crate::leanh::LeanObject,
    mut v_a_1611_: *mut crate::leanh::LeanObject,
    mut v_a_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(v_defaultPkg_1604_, v_self_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
    crate::leanh::lean_dec_ref(v_a_1610_);
    crate::leanh::lean_dec(v_a_1609_);
    crate::leanh::lean_dec(v_a_1608_);
    crate::leanh::lean_dec(v_a_1607_);
    return v_res_1613_;
}
pub unsafe fn _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: u8 = 0;
    let mut v_name_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = 1;
    v_name_1615_ = l_Lake_instDataKindFilePath;
    v___x_1616_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_1615_,
        v___x_1614_,
    );
    return v___x_1616_;
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(
    mut v_defaultPkg_1617_: *mut crate::leanh::LeanObject,
    mut v_self_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
    mut v_a_1620_: *mut crate::leanh::LeanObject,
    mut v_a_1621_: *mut crate::leanh::LeanObject,
    mut v_a_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
    mut v_a_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1632_: u8 = 0;
    let mut v_a_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1636_: u8 = 0;
    let mut v_kind_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v_unused_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1670_: u8 = 0;
    let mut v_unused_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1626_ = 1;
                crate::leanh::lean_inc_ref_n(v_self_1618_, 2);
                v___x_1627_ =
                    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
                        v_defaultPkg_1617_,
                        v_self_1618_,
                        v_self_1618_,
                        v___x_1626_,
                        v_a_1619_,
                        v_a_1620_,
                        v_a_1621_,
                        v_a_1622_,
                        v_a_1623_,
                        v_a_1624_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    crate::leanh::lean_inc(v_a_1628_);
                    v_snd_1629_ = crate::leanh::lean_ctor_get(v_a_1628_, 1);
                    v_isSharedCheck_1670_ = (!crate::leanh::lean_is_exclusive(v_a_1628_)) as u8;
                    if v_isSharedCheck_1670_ == 0 {
                        v_unused_1671_ = crate::leanh::lean_ctor_get(v_a_1628_, 0);
                        crate::leanh::lean_dec(v_unused_1671_);
                        v___x_1631_ = v_a_1628_;
                        v_isShared_1632_ = v_isSharedCheck_1670_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1629_);
                        crate::leanh::lean_dec(v_a_1628_);
                        v___x_1631_ = crate::leanh::lean_box(0);
                        v_isShared_1632_ = v_isSharedCheck_1670_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_self_1618_);
                    v_a_1672_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    v_a_1673_ = crate::leanh::lean_ctor_get(v___x_1627_, 1);
                    v_isSharedCheck_1680_ = (!crate::leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1680_ == 0 {
                        v___x_1675_ = v___x_1627_;
                        v_isShared_1676_ = v_isSharedCheck_1680_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1673_);
                        crate::leanh::lean_inc(v_a_1672_);
                        crate::leanh::lean_dec(v___x_1627_);
                        v___x_1675_ = crate::leanh::lean_box(0);
                        v_isShared_1676_ = v_isSharedCheck_1680_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1633_ = crate::leanh::lean_ctor_get(v___x_1627_, 1);
                v_isSharedCheck_1668_ = (!crate::leanh::lean_is_exclusive(v___x_1627_)) as u8;
                if v_isSharedCheck_1668_ == 0 {
                    v_unused_1669_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    crate::leanh::lean_dec(v_unused_1669_);
                    v___x_1635_ = v___x_1627_;
                    v_isShared_1636_ = v_isSharedCheck_1668_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1633_);
                    crate::leanh::lean_dec(v___x_1627_);
                    v___x_1635_ = crate::leanh::lean_box(0);
                    v_isShared_1636_ = v_isSharedCheck_1668_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_kind_1637_ = crate::leanh::lean_ctor_get(v_snd_1629_, 1);
                v_name_1638_ = l_Lake_instDataKindFilePath;
                v___x_1658_ = lean_name_eq(v_kind_1637_, v_name_1638_);
                if v___x_1658_ == 0 {
                    crate::leanh::lean_inc(v_kind_1637_);
                    crate::leanh::lean_del_object(v___x_1631_);
                    crate::leanh::lean_dec(v_snd_1629_);
                    v___x_1659_ = l_Lean_Name_isAnonymous(v_kind_1637_);
                    if v___x_1659_ == 0 {
                        v___x_1660_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4;
                        v___x_1661_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_1637_,
                                v___x_1626_,
                            );
                        v___x_1662_ = lean_string_append(v___x_1660_, v___x_1661_);
                        crate::leanh::lean_dec_ref(v___x_1661_);
                        v___x_1663_ = lean_string_append(v___x_1662_, v___x_1660_);
                        v___y_1640_ = v___x_1663_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_kind_1637_);
                        v___x_1664_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5;
                        v___y_1640_ = v___x_1664_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1635_);
                    crate::leanh::lean_dec_ref(v_self_1618_);
                    if v_isShared_1632_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1631_, 1, v_a_1633_);
                        crate::leanh::lean_ctor_set(v___x_1631_, 0, v_snd_1629_);
                        v___x_1666_ = v___x_1631_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_snd_1629_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_a_1633_);
                        v___x_1666_ = v_reuseFailAlloc_1667_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1641_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0;
                v___x_1642_ = l_Lake_PartialBuildKey_toString(v_self_1618_);
                v___x_1643_ = lean_string_append(v___x_1641_, v___x_1642_);
                crate::leanh::lean_dec_ref(v___x_1642_);
                v___x_1644_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1;
                v___x_1645_ = lean_string_append(v___x_1643_, v___x_1644_);
                v___x_1646_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0_once), _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0);
                v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
                v___x_1648_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3;
                v___x_1649_ = lean_string_append(v___x_1647_, v___x_1648_);
                v___x_1650_ = lean_string_append(v___x_1649_, v___y_1640_);
                crate::leanh::lean_dec_ref(v___y_1640_);
                v___x_1651_ = 3;
                v___x_1652_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1652_, 0, v___x_1650_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1652_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1651_,
                );
                v___x_1653_ = lean_array_get_size(v_a_1633_);
                v___x_1654_ = lean_array_push(v_a_1633_, v___x_1652_);
                if v_isShared_1636_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1635_, 1);
                    crate::leanh::lean_ctor_set(v___x_1635_, 1, v___x_1654_);
                    crate::leanh::lean_ctor_set(v___x_1635_, 0, v___x_1653_);
                    v___x_1656_ = v___x_1635_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1654_);
                    v___x_1656_ = v_reuseFailAlloc_1657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1656_;
            }
            5 => {
                return v___x_1666_;
            }
            6 => {
                if v_isShared_1676_ == 0 {
                    v___x_1678_ = v___x_1675_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1679_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_a_1673_);
                    v___x_1678_ = v_reuseFailAlloc_1679_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___boxed(
    mut v_defaultPkg_1681_: *mut crate::leanh::LeanObject,
    mut v_self_1682_: *mut crate::leanh::LeanObject,
    mut v_a_1683_: *mut crate::leanh::LeanObject,
    mut v_a_1684_: *mut crate::leanh::LeanObject,
    mut v_a_1685_: *mut crate::leanh::LeanObject,
    mut v_a_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1690_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(v_defaultPkg_1681_, v_self_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
    crate::leanh::lean_dec_ref(v_a_1687_);
    crate::leanh::lean_dec(v_a_1686_);
    crate::leanh::lean_dec(v_a_1685_);
    crate::leanh::lean_dec(v_a_1684_);
    return v_res_1690_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = crate::leanh::lean_box(0);
    v___x_1692_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1693_ = lean_mk_array(v___x_1692_, v___x_1691_);
    return v___x_1693_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0);
    v___x_1695_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
    crate::leanh::lean_ctor_set(v___x_1696_, 1, v___x_1694_);
    return v___x_1696_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2;
    v___x_1700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1);
    v___x_1701_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1701_, 0, v___x_1700_);
    crate::leanh::lean_ctor_set(v___x_1701_, 1, v___x_1699_);
    return v___x_1701_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3);
    return v___x_1702_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0()
-> u64 {
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u64 = 0;
    v___x_1703_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1704_ = lean_uint64_of_nat(v___x_1703_);
    return v___x_1704_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(
    mut v_x_1705_: *mut crate::leanh::LeanObject,
    mut v_x_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v_name_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: u64 = 0;
    let mut v___x_1717_: u64 = 0;
    let mut v___x_1718_: u64 = 0;
    let mut v_fold_1719_: u64 = 0;
    let mut v___x_1720_: u64 = 0;
    let mut v___x_1721_: u64 = 0;
    let mut v___x_1722_: u64 = 0;
    let mut v___x_1723_: usize = 0;
    let mut v___x_1724_: usize = 0;
    let mut v___x_1725_: usize = 0;
    let mut v___x_1726_: usize = 0;
    let mut v___x_1727_: usize = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u64 = 0;
    let mut v_hash_1735_: u64 = 0;
    let mut v_isSharedCheck_1736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1706_) == 0 {
                    return v_x_1705_;
                } else {
                    v_key_1707_ = crate::leanh::lean_ctor_get(v_x_1706_, 0);
                    v_value_1708_ = crate::leanh::lean_ctor_get(v_x_1706_, 1);
                    v_tail_1709_ = crate::leanh::lean_ctor_get(v_x_1706_, 2);
                    v_isSharedCheck_1736_ = (!crate::leanh::lean_is_exclusive(v_x_1706_)) as u8;
                    if v_isSharedCheck_1736_ == 0 {
                        v___x_1711_ = v_x_1706_;
                        v_isShared_1712_ = v_isSharedCheck_1736_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1709_);
                        crate::leanh::lean_inc(v_value_1708_);
                        crate::leanh::lean_inc(v_key_1707_);
                        crate::leanh::lean_dec(v_x_1706_);
                        v___x_1711_ = crate::leanh::lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1736_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_1713_ = crate::leanh::lean_ctor_get(v_key_1707_, 1);
                v___x_1714_ = lean_array_get_size(v_x_1705_);
                if crate::leanh::lean_obj_tag(v_name_1713_) == 0 {
                    v___x_1734_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
                    v___y_1716_ = v___x_1734_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1735_ = crate::leanh::lean_ctor_get_uint64(
                        v_name_1713_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1716_ = v_hash_1735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1717_ = 32u64;
                v___x_1718_ = lean_uint64_shift_right(v___y_1716_, v___x_1717_);
                v_fold_1719_ = lean_uint64_xor(v___y_1716_, v___x_1718_);
                v___x_1720_ = 16u64;
                v___x_1721_ = lean_uint64_shift_right(v_fold_1719_, v___x_1720_);
                v___x_1722_ = lean_uint64_xor(v_fold_1719_, v___x_1721_);
                v___x_1723_ = lean_uint64_to_usize(v___x_1722_);
                v___x_1724_ = lean_usize_of_nat(v___x_1714_);
                v___x_1725_ = 1usize;
                v___x_1726_ = lean_usize_sub(v___x_1724_, v___x_1725_);
                v___x_1727_ = lean_usize_land(v___x_1723_, v___x_1726_);
                v___x_1728_ = lean_array_uget_borrowed(v_x_1705_, v___x_1727_);
                crate::leanh::lean_inc(v___x_1728_);
                if v_isShared_1712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1711_, 2, v___x_1728_);
                    v___x_1730_ = v___x_1711_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1733_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_key_1707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_value_1708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 2, v___x_1728_);
                    v___x_1730_ = v_reuseFailAlloc_1733_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1731_ = lean_array_uset(v_x_1705_, v___x_1727_, v___x_1730_);
                v_x_1705_ = v___x_1731_;
                v_x_1706_ = v_tail_1709_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(
    mut v_i_1737_: *mut crate::leanh::LeanObject,
    mut v_source_1738_: *mut crate::leanh::LeanObject,
    mut v_target_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: u8 = 0;
    let mut v_es_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1740_ = lean_array_get_size(v_source_1738_);
                v___x_1741_ = lean_nat_dec_lt(v_i_1737_, v___x_1740_);
                if v___x_1741_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1738_);
                    crate::leanh::lean_dec(v_i_1737_);
                    return v_target_1739_;
                } else {
                    v_es_1742_ = lean_array_fget(v_source_1738_, v_i_1737_);
                    v___x_1743_ = crate::leanh::lean_box(0);
                    v_source_1744_ = lean_array_fset(v_source_1738_, v_i_1737_, v___x_1743_);
                    v_target_1745_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(v_target_1739_, v_es_1742_);
                    v___x_1746_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1747_ = lean_nat_add(v_i_1737_, v___x_1746_);
                    crate::leanh::lean_dec(v_i_1737_);
                    v_i_1737_ = v___x_1747_;
                    v_source_1738_ = v_source_1744_;
                    v_target_1739_ = v_target_1745_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(
    mut v_data_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = lean_array_get_size(v_data_1749_);
    v___x_1751_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1752_ = lean_nat_mul(v___x_1750_, v___x_1751_);
    v___x_1753_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1754_ = crate::leanh::lean_box(0);
    v___x_1755_ = lean_mk_array(v_nbuckets_1752_, v___x_1754_);
    v___x_1756_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(v___x_1753_, v_data_1749_, v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_x_1758_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1759_: u8 = 0;
    let mut v_key_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1758_) == 0 {
                    v___x_1759_ = 0;
                    return v___x_1759_;
                } else {
                    v_key_1760_ = crate::leanh::lean_ctor_get(v_x_1758_, 0);
                    v_tail_1761_ = crate::leanh::lean_ctor_get(v_x_1758_, 2);
                    v_name_1762_ = crate::leanh::lean_ctor_get(v_key_1760_, 1);
                    v_name_1763_ = crate::leanh::lean_ctor_get(v_a_1757_, 1);
                    v___x_1764_ = lean_name_eq(v_name_1762_, v_name_1763_);
                    if v___x_1764_ == 0 {
                        v_x_1758_ = v_tail_1761_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1764_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_x_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1768_: u8 = 0;
    let mut v_r_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(v_a_1766_, v_x_1767_);
    crate::leanh::lean_dec(v_x_1767_);
    crate::leanh::lean_dec_ref(v_a_1766_);
    v_r_1769_ = crate::leanh::lean_box((v_res_1768_) as usize);
    return v_r_1769_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(
    mut v_m_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_b_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1778_: u64 = 0;
    let mut v___x_1779_: u64 = 0;
    let mut v___x_1780_: u64 = 0;
    let mut v_fold_1781_: u64 = 0;
    let mut v___x_1782_: u64 = 0;
    let mut v___x_1783_: u64 = 0;
    let mut v___x_1784_: u64 = 0;
    let mut v___x_1785_: usize = 0;
    let mut v___x_1786_: usize = 0;
    let mut v___x_1787_: usize = 0;
    let mut v___x_1788_: usize = 0;
    let mut v___x_1789_: usize = 0;
    let mut v_bkt_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v_val_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u64 = 0;
    let mut v_hash_1816_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1773_ = crate::leanh::lean_ctor_get(v_m_1770_, 0);
                v_buckets_1774_ = crate::leanh::lean_ctor_get(v_m_1770_, 1);
                v_name_1775_ = crate::leanh::lean_ctor_get(v_a_1771_, 1);
                v___x_1776_ = lean_array_get_size(v_buckets_1774_);
                if crate::leanh::lean_obj_tag(v_name_1775_) == 0 {
                    v___x_1815_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
                    v___y_1778_ = v___x_1815_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1816_ = crate::leanh::lean_ctor_get_uint64(
                        v_name_1775_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1778_ = v_hash_1816_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1779_ = 32u64;
                v___x_1780_ = lean_uint64_shift_right(v___y_1778_, v___x_1779_);
                v_fold_1781_ = lean_uint64_xor(v___y_1778_, v___x_1780_);
                v___x_1782_ = 16u64;
                v___x_1783_ = lean_uint64_shift_right(v_fold_1781_, v___x_1782_);
                v___x_1784_ = lean_uint64_xor(v_fold_1781_, v___x_1783_);
                v___x_1785_ = lean_uint64_to_usize(v___x_1784_);
                v___x_1786_ = lean_usize_of_nat(v___x_1776_);
                v___x_1787_ = 1usize;
                v___x_1788_ = lean_usize_sub(v___x_1786_, v___x_1787_);
                v___x_1789_ = lean_usize_land(v___x_1785_, v___x_1788_);
                v_bkt_1790_ = lean_array_uget_borrowed(v_buckets_1774_, v___x_1789_);
                v___x_1791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(v_a_1771_, v_bkt_1790_);
                if v___x_1791_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1774_);
                    crate::leanh::lean_inc(v_size_1773_);
                    v_isSharedCheck_1812_ = (!crate::leanh::lean_is_exclusive(v_m_1770_)) as u8;
                    if v_isSharedCheck_1812_ == 0 {
                        v_unused_1813_ = crate::leanh::lean_ctor_get(v_m_1770_, 1);
                        crate::leanh::lean_dec(v_unused_1813_);
                        v_unused_1814_ = crate::leanh::lean_ctor_get(v_m_1770_, 0);
                        crate::leanh::lean_dec(v_unused_1814_);
                        v___x_1793_ = v_m_1770_;
                        v_isShared_1794_ = v_isSharedCheck_1812_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1770_);
                        v___x_1793_ = crate::leanh::lean_box(0);
                        v_isShared_1794_ = v_isSharedCheck_1812_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1772_);
                    crate::leanh::lean_dec_ref(v_a_1771_);
                    return v_m_1770_;
                }
            }
            2 => {
                v___x_1795_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1796_ = lean_nat_add(v_size_1773_, v___x_1795_);
                crate::leanh::lean_dec(v_size_1773_);
                crate::leanh::lean_inc(v_bkt_1790_);
                v___x_1797_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1797_, 0, v_a_1771_);
                crate::leanh::lean_ctor_set(v___x_1797_, 1, v_b_1772_);
                crate::leanh::lean_ctor_set(v___x_1797_, 2, v_bkt_1790_);
                v_buckets_x27_1798_ = lean_array_uset(v_buckets_1774_, v___x_1789_, v___x_1797_);
                v___x_1799_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1800_ = lean_nat_mul(v_size_x27_1796_, v___x_1799_);
                v___x_1801_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1802_ = lean_nat_div(v___x_1800_, v___x_1801_);
                crate::leanh::lean_dec(v___x_1800_);
                v___x_1803_ = lean_array_get_size(v_buckets_x27_1798_);
                v___x_1804_ = lean_nat_dec_le(v___x_1802_, v___x_1803_);
                crate::leanh::lean_dec(v___x_1802_);
                if v___x_1804_ == 0 {
                    v_val_1805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(v_buckets_x27_1798_);
                    if v_isShared_1794_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1793_, 1, v_val_1805_);
                        crate::leanh::lean_ctor_set(v___x_1793_, 0, v_size_x27_1796_);
                        v___x_1807_ = v___x_1793_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_size_x27_1796_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_val_1805_);
                        v___x_1807_ = v_reuseFailAlloc_1808_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1794_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1793_, 1, v_buckets_x27_1798_);
                        crate::leanh::lean_ctor_set(v___x_1793_, 0, v_size_x27_1796_);
                        v___x_1810_ = v___x_1793_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_size_x27_1796_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_buckets_x27_1798_);
                        v___x_1810_ = v_reuseFailAlloc_1811_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1807_;
            }
            4 => {
                return v___x_1810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(
    mut v_m_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1823_: u64 = 0;
    let mut v___x_1824_: u64 = 0;
    let mut v___x_1825_: u64 = 0;
    let mut v_fold_1826_: u64 = 0;
    let mut v___x_1827_: u64 = 0;
    let mut v___x_1828_: u64 = 0;
    let mut v___x_1829_: u64 = 0;
    let mut v___x_1830_: usize = 0;
    let mut v___x_1831_: usize = 0;
    let mut v___x_1832_: usize = 0;
    let mut v___x_1833_: usize = 0;
    let mut v___x_1834_: usize = 0;
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: u64 = 0;
    let mut v_hash_1838_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1819_ = crate::leanh::lean_ctor_get(v_m_1817_, 1);
                v_name_1820_ = crate::leanh::lean_ctor_get(v_a_1818_, 1);
                v___x_1821_ = lean_array_get_size(v_buckets_1819_);
                if crate::leanh::lean_obj_tag(v_name_1820_) == 0 {
                    v___x_1837_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
                    v___y_1823_ = v___x_1837_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1838_ = crate::leanh::lean_ctor_get_uint64(
                        v_name_1820_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1823_ = v_hash_1838_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1824_ = 32u64;
                v___x_1825_ = lean_uint64_shift_right(v___y_1823_, v___x_1824_);
                v_fold_1826_ = lean_uint64_xor(v___y_1823_, v___x_1825_);
                v___x_1827_ = 16u64;
                v___x_1828_ = lean_uint64_shift_right(v_fold_1826_, v___x_1827_);
                v___x_1829_ = lean_uint64_xor(v_fold_1826_, v___x_1828_);
                v___x_1830_ = lean_uint64_to_usize(v___x_1829_);
                v___x_1831_ = lean_usize_of_nat(v___x_1821_);
                v___x_1832_ = 1usize;
                v___x_1833_ = lean_usize_sub(v___x_1831_, v___x_1832_);
                v___x_1834_ = lean_usize_land(v___x_1830_, v___x_1833_);
                v___x_1835_ = lean_array_uget_borrowed(v_buckets_1819_, v___x_1834_);
                v___x_1836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(v_a_1818_, v___x_1835_);
                return v___x_1836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg___boxed(
    mut v_m_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1841_: u8 = 0;
    let mut v_r_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(v_m_1839_, v_a_1840_);
    crate::leanh::lean_dec_ref(v_a_1840_);
    crate::leanh::lean_dec_ref(v_m_1839_);
    v_r_1842_ = crate::leanh::lean_box((v_res_1841_) as usize);
    return v_r_1842_;
}
pub unsafe fn l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(
    mut v_self_1843_: *mut crate::leanh::LeanObject,
    mut v_a_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toHashSet_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toArray_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1857_: u8 = 0;
    let mut v_unused_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toHashSet_1845_ = crate::leanh::lean_ctor_get(v_self_1843_, 0);
                v_toArray_1846_ = crate::leanh::lean_ctor_get(v_self_1843_, 1);
                v___x_1847_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(v_toHashSet_1845_, v_a_1844_);
                if v___x_1847_ == 0 {
                    crate::leanh::lean_inc_ref(v_toArray_1846_);
                    crate::leanh::lean_inc_ref(v_toHashSet_1845_);
                    v_isSharedCheck_1857_ = (!crate::leanh::lean_is_exclusive(v_self_1843_)) as u8;
                    if v_isSharedCheck_1857_ == 0 {
                        v_unused_1858_ = crate::leanh::lean_ctor_get(v_self_1843_, 1);
                        crate::leanh::lean_dec(v_unused_1858_);
                        v_unused_1859_ = crate::leanh::lean_ctor_get(v_self_1843_, 0);
                        crate::leanh::lean_dec(v_unused_1859_);
                        v___x_1849_ = v_self_1843_;
                        v_isShared_1850_ = v_isSharedCheck_1857_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_self_1843_);
                        v___x_1849_ = crate::leanh::lean_box(0);
                        v_isShared_1850_ = v_isSharedCheck_1857_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1844_);
                    return v_self_1843_;
                }
            }
            1 => {
                v___x_1851_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_a_1844_);
                v___x_1852_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(v_toHashSet_1845_, v_a_1844_, v___x_1851_);
                v___x_1853_ = lean_array_push(v_toArray_1846_, v_a_1844_);
                if v_isShared_1850_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1849_, 1, v___x_1853_);
                    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1852_);
                    v___x_1855_ = v___x_1849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1856_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1853_);
                    v___x_1855_ = v_reuseFailAlloc_1856_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(
    mut v_as_1860_: *mut crate::leanh::LeanObject,
    mut v_i_1861_: usize,
    mut v_stop_1862_: usize,
    mut v_b_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lib_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: usize = 0;
    let mut v___x_1869_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1864_ = lean_usize_dec_eq(v_i_1861_, v_stop_1862_);
                if v___x_1864_ == 0 {
                    v___x_1865_ = lean_array_uget_borrowed(v_as_1860_, v_i_1861_);
                    v_lib_1866_ = crate::leanh::lean_ctor_get(v___x_1865_, 0);
                    crate::leanh::lean_inc_ref(v_lib_1866_);
                    v___x_1867_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(v_b_1863_, v_lib_1866_);
                    v___x_1868_ = 1usize;
                    v___x_1869_ = lean_usize_add(v_i_1861_, v___x_1868_);
                    v_i_1861_ = v___x_1869_;
                    v_b_1863_ = v___x_1867_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1863_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14___boxed(
    mut v_as_1871_: *mut crate::leanh::LeanObject,
    mut v_i_1872_: *mut crate::leanh::LeanObject,
    mut v_stop_1873_: *mut crate::leanh::LeanObject,
    mut v_b_1874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1875_: usize = 0;
    let mut v_stop_boxed_1876_: usize = 0;
    let mut v_res_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1875_ = crate::leanh::lean_unbox_usize(v_i_1872_);
    crate::leanh::lean_dec(v_i_1872_);
    v_stop_boxed_1876_ = crate::leanh::lean_unbox_usize(v_stop_1873_);
    crate::leanh::lean_dec(v_stop_1873_);
    v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(v_as_1871_, v_i_boxed_1875_, v_stop_boxed_1876_, v_b_1874_);
    crate::leanh::lean_dec_ref(v_as_1871_);
    return v_res_1877_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(
    mut v___x_1878_: *mut crate::leanh::LeanObject,
    mut v_as_1879_: *mut crate::leanh::LeanObject,
    mut v_sz_1880_: usize,
    mut v_i_1881_: usize,
    mut v_b_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: usize = 0;
    let mut v___x_1898_: usize = 0;
    let mut v_a_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1890_ = lean_usize_dec_lt(v_i_1881_, v_sz_1880_);
                if v___x_1890_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1883_);
                    crate::leanh::lean_dec_ref(v___x_1878_);
                    v___x_1891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1891_, 0, v_b_1882_);
                    crate::leanh::lean_ctor_set(v___x_1891_, 1, v___y_1888_);
                    return v___x_1891_;
                } else {
                    v_a_1892_ = lean_array_uget_borrowed(v_as_1879_, v_i_1881_);
                    crate::leanh::lean_inc_ref(v___y_1883_);
                    crate::leanh::lean_inc(v_a_1892_);
                    crate::leanh::lean_inc_ref(v___x_1878_);
                    v___x_1893_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(v___x_1878_, v_a_1892_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
                    if crate::leanh::lean_obj_tag(v___x_1893_) == 0 {
                        v_a_1894_ = crate::leanh::lean_ctor_get(v___x_1893_, 0);
                        crate::leanh::lean_inc(v_a_1894_);
                        v_a_1895_ = crate::leanh::lean_ctor_get(v___x_1893_, 1);
                        crate::leanh::lean_inc(v_a_1895_);
                        crate::leanh::lean_dec_ref_known(v___x_1893_, 2);
                        v___x_1896_ = lean_array_push(v_b_1882_, v_a_1894_);
                        v___x_1897_ = 1usize;
                        v___x_1898_ = lean_usize_add(v_i_1881_, v___x_1897_);
                        v_i_1881_ = v___x_1898_;
                        v_b_1882_ = v___x_1896_;
                        v___y_1888_ = v_a_1895_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1883_);
                        crate::leanh::lean_dec_ref(v_b_1882_);
                        crate::leanh::lean_dec_ref(v___x_1878_);
                        v_a_1900_ = crate::leanh::lean_ctor_get(v___x_1893_, 0);
                        v_a_1901_ = crate::leanh::lean_ctor_get(v___x_1893_, 1);
                        v_isSharedCheck_1908_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1893_)) as u8;
                        if v_isSharedCheck_1908_ == 0 {
                            v___x_1903_ = v___x_1893_;
                            v_isShared_1904_ = v_isSharedCheck_1908_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1901_);
                            crate::leanh::lean_inc(v_a_1900_);
                            crate::leanh::lean_dec(v___x_1893_);
                            v___x_1903_ = crate::leanh::lean_box(0);
                            v_isShared_1904_ = v_isSharedCheck_1908_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1904_ == 0 {
                    v___x_1906_ = v___x_1903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_a_1901_);
                    v___x_1906_ = v_reuseFailAlloc_1907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11___boxed(
    mut v___x_1909_: *mut crate::leanh::LeanObject,
    mut v_as_1910_: *mut crate::leanh::LeanObject,
    mut v_sz_1911_: *mut crate::leanh::LeanObject,
    mut v_i_1912_: *mut crate::leanh::LeanObject,
    mut v_b_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1921_: usize = 0;
    let mut v_i_boxed_1922_: usize = 0;
    let mut v_res_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1921_ = crate::leanh::lean_unbox_usize(v_sz_1911_);
    crate::leanh::lean_dec(v_sz_1911_);
    v_i_boxed_1922_ = crate::leanh::lean_unbox_usize(v_i_1912_);
    crate::leanh::lean_dec(v_i_1912_);
    v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(v___x_1909_, v_as_1910_, v_sz_boxed_1921_, v_i_boxed_1922_, v_b_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
    crate::leanh::lean_dec_ref(v___y_1918_);
    crate::leanh::lean_dec(v___y_1917_);
    crate::leanh::lean_dec(v___y_1916_);
    crate::leanh::lean_dec(v___y_1915_);
    crate::leanh::lean_dec_ref(v_as_1910_);
    return v_res_1923_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(
    mut v_a_1924_: *mut crate::leanh::LeanObject,
    mut v_as_1925_: *mut crate::leanh::LeanObject,
    mut v_sz_1926_: usize,
    mut v_i_1927_: usize,
    mut v_b_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
    mut v___y_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1936_: u8 = 0;
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: usize = 0;
    let mut v_a_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1936_ = lean_usize_dec_lt(v_i_1927_, v_sz_1926_);
                if v___x_1936_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1929_);
                    crate::leanh::lean_dec_ref(v_a_1924_);
                    v___x_1937_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1937_, 0, v_b_1928_);
                    crate::leanh::lean_ctor_set(v___x_1937_, 1, v___y_1934_);
                    return v___x_1937_;
                } else {
                    v_pkg_1938_ = crate::leanh::lean_ctor_get(v_a_1924_, 0);
                    v_a_1939_ = lean_array_uget_borrowed(v_as_1925_, v_i_1927_);
                    crate::leanh::lean_inc_ref(v___y_1929_);
                    crate::leanh::lean_inc(v_a_1939_);
                    crate::leanh::lean_inc_ref(v_pkg_1938_);
                    v___x_1940_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(v_pkg_1938_, v_a_1939_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
                    if crate::leanh::lean_obj_tag(v___x_1940_) == 0 {
                        v_a_1941_ = crate::leanh::lean_ctor_get(v___x_1940_, 0);
                        crate::leanh::lean_inc(v_a_1941_);
                        v_a_1942_ = crate::leanh::lean_ctor_get(v___x_1940_, 1);
                        crate::leanh::lean_inc(v_a_1942_);
                        crate::leanh::lean_dec_ref_known(v___x_1940_, 2);
                        v___x_1943_ = lean_array_push(v_b_1928_, v_a_1941_);
                        v___x_1944_ = 1usize;
                        v___x_1945_ = lean_usize_add(v_i_1927_, v___x_1944_);
                        v_i_1927_ = v___x_1945_;
                        v_b_1928_ = v___x_1943_;
                        v___y_1934_ = v_a_1942_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1929_);
                        crate::leanh::lean_dec_ref(v_b_1928_);
                        crate::leanh::lean_dec_ref(v_a_1924_);
                        v_a_1947_ = crate::leanh::lean_ctor_get(v___x_1940_, 0);
                        v_a_1948_ = crate::leanh::lean_ctor_get(v___x_1940_, 1);
                        v_isSharedCheck_1955_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1940_)) as u8;
                        if v_isSharedCheck_1955_ == 0 {
                            v___x_1950_ = v___x_1940_;
                            v_isShared_1951_ = v_isSharedCheck_1955_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1948_);
                            crate::leanh::lean_inc(v_a_1947_);
                            crate::leanh::lean_dec(v___x_1940_);
                            v___x_1950_ = crate::leanh::lean_box(0);
                            v_isShared_1951_ = v_isSharedCheck_1955_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1951_ == 0 {
                    v___x_1953_ = v___x_1950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_a_1948_);
                    v___x_1953_ = v_reuseFailAlloc_1954_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6___boxed(
    mut v_a_1956_: *mut crate::leanh::LeanObject,
    mut v_as_1957_: *mut crate::leanh::LeanObject,
    mut v_sz_1958_: *mut crate::leanh::LeanObject,
    mut v_i_1959_: *mut crate::leanh::LeanObject,
    mut v_b_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1968_: usize = 0;
    let mut v_i_boxed_1969_: usize = 0;
    let mut v_res_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1968_ = crate::leanh::lean_unbox_usize(v_sz_1958_);
    crate::leanh::lean_dec(v_sz_1958_);
    v_i_boxed_1969_ = crate::leanh::lean_unbox_usize(v_i_1959_);
    crate::leanh::lean_dec(v_i_1959_);
    v_res_1970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(v_a_1956_, v_as_1957_, v_sz_boxed_1968_, v_i_boxed_1969_, v_b_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
    crate::leanh::lean_dec_ref(v___y_1965_);
    crate::leanh::lean_dec(v___y_1964_);
    crate::leanh::lean_dec(v___y_1963_);
    crate::leanh::lean_dec(v___y_1962_);
    crate::leanh::lean_dec_ref(v_as_1957_);
    return v_res_1970_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(
    mut v_a_1971_: *mut crate::leanh::LeanObject,
    mut v_as_1972_: *mut crate::leanh::LeanObject,
    mut v_sz_1973_: usize,
    mut v_i_1974_: usize,
    mut v_b_1975_: *mut crate::leanh::LeanObject,
    mut v___y_1976_: *mut crate::leanh::LeanObject,
    mut v___y_1977_: *mut crate::leanh::LeanObject,
    mut v___y_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: usize = 0;
    let mut v_a_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1983_ = lean_usize_dec_lt(v_i_1974_, v_sz_1973_);
                if v___x_1983_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1976_);
                    crate::leanh::lean_dec_ref(v_a_1971_);
                    v___x_1984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1984_, 0, v_b_1975_);
                    crate::leanh::lean_ctor_set(v___x_1984_, 1, v___y_1981_);
                    return v___x_1984_;
                } else {
                    v_pkg_1985_ = crate::leanh::lean_ctor_get(v_a_1971_, 0);
                    v_a_1986_ = lean_array_uget_borrowed(v_as_1972_, v_i_1974_);
                    crate::leanh::lean_inc_ref(v___y_1976_);
                    crate::leanh::lean_inc(v_a_1986_);
                    crate::leanh::lean_inc_ref(v_pkg_1985_);
                    v___x_1987_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(v_pkg_1985_, v_a_1986_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
                    if crate::leanh::lean_obj_tag(v___x_1987_) == 0 {
                        v_a_1988_ = crate::leanh::lean_ctor_get(v___x_1987_, 0);
                        crate::leanh::lean_inc(v_a_1988_);
                        v_a_1989_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                        crate::leanh::lean_inc(v_a_1989_);
                        crate::leanh::lean_dec_ref_known(v___x_1987_, 2);
                        v___x_1990_ = lean_array_push(v_b_1975_, v_a_1988_);
                        v___x_1991_ = 1usize;
                        v___x_1992_ = lean_usize_add(v_i_1974_, v___x_1991_);
                        v_i_1974_ = v___x_1992_;
                        v_b_1975_ = v___x_1990_;
                        v___y_1981_ = v_a_1989_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1976_);
                        crate::leanh::lean_dec_ref(v_b_1975_);
                        crate::leanh::lean_dec_ref(v_a_1971_);
                        v_a_1994_ = crate::leanh::lean_ctor_get(v___x_1987_, 0);
                        v_a_1995_ = crate::leanh::lean_ctor_get(v___x_1987_, 1);
                        v_isSharedCheck_2002_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1987_)) as u8;
                        if v_isSharedCheck_2002_ == 0 {
                            v___x_1997_ = v___x_1987_;
                            v_isShared_1998_ = v_isSharedCheck_2002_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1995_);
                            crate::leanh::lean_inc(v_a_1994_);
                            crate::leanh::lean_dec(v___x_1987_);
                            v___x_1997_ = crate::leanh::lean_box(0);
                            v_isShared_1998_ = v_isSharedCheck_2002_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1998_ == 0 {
                    v___x_2000_ = v___x_1997_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_a_1995_);
                    v___x_2000_ = v_reuseFailAlloc_2001_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5___boxed(
    mut v_a_2003_: *mut crate::leanh::LeanObject,
    mut v_as_2004_: *mut crate::leanh::LeanObject,
    mut v_sz_2005_: *mut crate::leanh::LeanObject,
    mut v_i_2006_: *mut crate::leanh::LeanObject,
    mut v_b_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
    mut v___y_2009_: *mut crate::leanh::LeanObject,
    mut v___y_2010_: *mut crate::leanh::LeanObject,
    mut v___y_2011_: *mut crate::leanh::LeanObject,
    mut v___y_2012_: *mut crate::leanh::LeanObject,
    mut v___y_2013_: *mut crate::leanh::LeanObject,
    mut v___y_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2015_: usize = 0;
    let mut v_i_boxed_2016_: usize = 0;
    let mut v_res_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2015_ = crate::leanh::lean_unbox_usize(v_sz_2005_);
    crate::leanh::lean_dec(v_sz_2005_);
    v_i_boxed_2016_ = crate::leanh::lean_unbox_usize(v_i_2006_);
    crate::leanh::lean_dec(v_i_2006_);
    v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(v_a_2003_, v_as_2004_, v_sz_boxed_2015_, v_i_boxed_2016_, v_b_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
    crate::leanh::lean_dec_ref(v___y_2012_);
    crate::leanh::lean_dec(v___y_2011_);
    crate::leanh::lean_dec(v___y_2010_);
    crate::leanh::lean_dec(v___y_2009_);
    crate::leanh::lean_dec_ref(v_as_2004_);
    return v_res_2017_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(
    mut v_as_2018_: *mut crate::leanh::LeanObject,
    mut v_sz_2019_: usize,
    mut v_i_2020_: usize,
    mut v_b_2021_: *mut crate::leanh::LeanObject,
    mut v___y_2022_: *mut crate::leanh::LeanObject,
    mut v___y_2023_: *mut crate::leanh::LeanObject,
    mut v___y_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2039_: u8 = 0;
    let mut v_a_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2051_: usize = 0;
    let mut v___x_2052_: usize = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2057_: usize = 0;
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: usize = 0;
    let mut v_reuseFailAlloc_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2033_ = lean_usize_dec_lt(v_i_2020_, v_sz_2019_);
                if v___x_2033_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2022_);
                    v___x_2034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2034_, 0, v_b_2021_);
                    crate::leanh::lean_ctor_set(v___x_2034_, 1, v___y_2027_);
                    return v___x_2034_;
                } else {
                    v_fst_2035_ = crate::leanh::lean_ctor_get(v_b_2021_, 0);
                    v_snd_2036_ = crate::leanh::lean_ctor_get(v_b_2021_, 1);
                    v_isSharedCheck_2071_ = (!crate::leanh::lean_is_exclusive(v_b_2021_)) as u8;
                    if v_isSharedCheck_2071_ == 0 {
                        v___x_2038_ = v_b_2021_;
                        v_isShared_2039_ = v_isSharedCheck_2071_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2036_);
                        crate::leanh::lean_inc(v_fst_2035_);
                        crate::leanh::lean_dec(v_b_2021_);
                        v___x_2038_ = crate::leanh::lean_box(0);
                        v_isShared_2039_ = v_isSharedCheck_2071_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2032_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2032_, 0, v_a_2030_);
                crate::leanh::lean_ctor_set(v___x_2032_, 1, v_a_2031_);
                return v___x_2032_;
            }
            2 => {
                v_a_2040_ = lean_array_uget_borrowed(v_as_2018_, v_i_2020_);
                v_pkg_2041_ = crate::leanh::lean_ctor_get(v_a_2040_, 0);
                v_config_2042_ = crate::leanh::lean_ctor_get(v_pkg_2041_, 6);
                v_toLeanConfig_2043_ = crate::leanh::lean_ctor_get(v_config_2042_, 1);
                v_config_2044_ = crate::leanh::lean_ctor_get(v_a_2040_, 2);
                v_toLeanConfig_2045_ = crate::leanh::lean_ctor_get(v_config_2044_, 0);
                v_moreLinkObjs_2046_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2043_, 6);
                v_moreLinkLibs_2047_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2043_, 7);
                v_moreLinkObjs_2048_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2045_, 6);
                v_moreLinkLibs_2049_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2045_, 7);
                crate::leanh::lean_inc_ref(v_moreLinkObjs_2046_);
                v___x_2050_ = l_Array_append___redArg(v_moreLinkObjs_2046_, v_moreLinkObjs_2048_);
                v_sz_2051_ = lean_array_size(v___x_2050_);
                v___x_2052_ = 0usize;
                crate::leanh::lean_inc_ref(v___y_2022_);
                crate::leanh::lean_inc(v_a_2040_);
                v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(v_a_2040_, v___x_2050_, v_sz_2051_, v___x_2052_, v_fst_2035_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
                crate::leanh::lean_dec_ref(v___x_2050_);
                if crate::leanh::lean_obj_tag(v___x_2053_) == 0 {
                    v_a_2054_ = crate::leanh::lean_ctor_get(v___x_2053_, 0);
                    crate::leanh::lean_inc(v_a_2054_);
                    v_a_2055_ = crate::leanh::lean_ctor_get(v___x_2053_, 1);
                    crate::leanh::lean_inc(v_a_2055_);
                    crate::leanh::lean_dec_ref_known(v___x_2053_, 2);
                    crate::leanh::lean_inc_ref(v_moreLinkLibs_2047_);
                    v___x_2056_ =
                        l_Array_append___redArg(v_moreLinkLibs_2047_, v_moreLinkLibs_2049_);
                    v_sz_2057_ = lean_array_size(v___x_2056_);
                    crate::leanh::lean_inc_ref(v___y_2022_);
                    crate::leanh::lean_inc(v_a_2040_);
                    v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(v_a_2040_, v___x_2056_, v_sz_2057_, v___x_2052_, v_snd_2036_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v_a_2055_);
                    crate::leanh::lean_dec_ref(v___x_2056_);
                    if crate::leanh::lean_obj_tag(v___x_2058_) == 0 {
                        v_a_2059_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                        crate::leanh::lean_inc(v_a_2059_);
                        v_a_2060_ = crate::leanh::lean_ctor_get(v___x_2058_, 1);
                        crate::leanh::lean_inc(v_a_2060_);
                        crate::leanh::lean_dec_ref_known(v___x_2058_, 2);
                        if v_isShared_2039_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2038_, 1, v_a_2059_);
                            crate::leanh::lean_ctor_set(v___x_2038_, 0, v_a_2054_);
                            v___x_2062_ = v___x_2038_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2066_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2054_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_a_2059_);
                            v___x_2062_ = v_reuseFailAlloc_2066_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2054_);
                        crate::leanh::lean_del_object(v___x_2038_);
                        crate::leanh::lean_dec_ref(v___y_2022_);
                        v_a_2067_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
                        crate::leanh::lean_inc(v_a_2067_);
                        v_a_2068_ = crate::leanh::lean_ctor_get(v___x_2058_, 1);
                        crate::leanh::lean_inc(v_a_2068_);
                        crate::leanh::lean_dec_ref_known(v___x_2058_, 2);
                        v_a_2030_ = v_a_2067_;
                        v_a_2031_ = v_a_2068_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2038_);
                    crate::leanh::lean_dec(v_snd_2036_);
                    crate::leanh::lean_dec_ref(v___y_2022_);
                    v_a_2069_ = crate::leanh::lean_ctor_get(v___x_2053_, 0);
                    crate::leanh::lean_inc(v_a_2069_);
                    v_a_2070_ = crate::leanh::lean_ctor_get(v___x_2053_, 1);
                    crate::leanh::lean_inc(v_a_2070_);
                    crate::leanh::lean_dec_ref_known(v___x_2053_, 2);
                    v_a_2030_ = v_a_2069_;
                    v_a_2031_ = v_a_2070_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2063_ = 1usize;
                v___x_2064_ = lean_usize_add(v_i_2020_, v___x_2063_);
                v_i_2020_ = v___x_2064_;
                v_b_2021_ = v___x_2062_;
                v___y_2027_ = v_a_2060_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10___boxed(
    mut v_as_2072_: *mut crate::leanh::LeanObject,
    mut v_sz_2073_: *mut crate::leanh::LeanObject,
    mut v_i_2074_: *mut crate::leanh::LeanObject,
    mut v_b_2075_: *mut crate::leanh::LeanObject,
    mut v___y_2076_: *mut crate::leanh::LeanObject,
    mut v___y_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2083_: usize = 0;
    let mut v_i_boxed_2084_: usize = 0;
    let mut v_res_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2083_ = crate::leanh::lean_unbox_usize(v_sz_2073_);
    crate::leanh::lean_dec(v_sz_2073_);
    v_i_boxed_2084_ = crate::leanh::lean_unbox_usize(v_i_2074_);
    crate::leanh::lean_dec(v_i_2074_);
    v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(v_as_2072_, v_sz_boxed_2083_, v_i_boxed_2084_, v_b_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
    crate::leanh::lean_dec_ref(v___y_2080_);
    crate::leanh::lean_dec(v___y_2079_);
    crate::leanh::lean_dec(v___y_2078_);
    crate::leanh::lean_dec(v___y_2077_);
    crate::leanh::lean_dec_ref(v_as_2072_);
    return v_res_2085_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(
    mut v___x_2086_: *mut crate::leanh::LeanObject,
    mut v_as_2087_: *mut crate::leanh::LeanObject,
    mut v_sz_2088_: usize,
    mut v_i_2089_: usize,
    mut v_b_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
    mut v___y_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: usize = 0;
    let mut v___x_2106_: usize = 0;
    let mut v_a_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2098_ = lean_usize_dec_lt(v_i_2089_, v_sz_2088_);
                if v___x_2098_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2091_);
                    crate::leanh::lean_dec_ref(v___x_2086_);
                    v___x_2099_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2099_, 0, v_b_2090_);
                    crate::leanh::lean_ctor_set(v___x_2099_, 1, v___y_2096_);
                    return v___x_2099_;
                } else {
                    v_a_2100_ = lean_array_uget_borrowed(v_as_2087_, v_i_2089_);
                    crate::leanh::lean_inc_ref(v___y_2091_);
                    crate::leanh::lean_inc(v_a_2100_);
                    crate::leanh::lean_inc_ref(v___x_2086_);
                    v___x_2101_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(v___x_2086_, v_a_2100_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
                    if crate::leanh::lean_obj_tag(v___x_2101_) == 0 {
                        v_a_2102_ = crate::leanh::lean_ctor_get(v___x_2101_, 0);
                        crate::leanh::lean_inc(v_a_2102_);
                        v_a_2103_ = crate::leanh::lean_ctor_get(v___x_2101_, 1);
                        crate::leanh::lean_inc(v_a_2103_);
                        crate::leanh::lean_dec_ref_known(v___x_2101_, 2);
                        v___x_2104_ = lean_array_push(v_b_2090_, v_a_2102_);
                        v___x_2105_ = 1usize;
                        v___x_2106_ = lean_usize_add(v_i_2089_, v___x_2105_);
                        v_i_2089_ = v___x_2106_;
                        v_b_2090_ = v___x_2104_;
                        v___y_2096_ = v_a_2103_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2091_);
                        crate::leanh::lean_dec_ref(v_b_2090_);
                        crate::leanh::lean_dec_ref(v___x_2086_);
                        v_a_2108_ = crate::leanh::lean_ctor_get(v___x_2101_, 0);
                        v_a_2109_ = crate::leanh::lean_ctor_get(v___x_2101_, 1);
                        v_isSharedCheck_2116_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2101_)) as u8;
                        if v_isSharedCheck_2116_ == 0 {
                            v___x_2111_ = v___x_2101_;
                            v_isShared_2112_ = v_isSharedCheck_2116_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2109_);
                            crate::leanh::lean_inc(v_a_2108_);
                            crate::leanh::lean_dec(v___x_2101_);
                            v___x_2111_ = crate::leanh::lean_box(0);
                            v_isShared_2112_ = v_isSharedCheck_2116_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2112_ == 0 {
                    v___x_2114_ = v___x_2111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_a_2109_);
                    v___x_2114_ = v_reuseFailAlloc_2115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9___boxed(
    mut v___x_2117_: *mut crate::leanh::LeanObject,
    mut v_as_2118_: *mut crate::leanh::LeanObject,
    mut v_sz_2119_: *mut crate::leanh::LeanObject,
    mut v_i_2120_: *mut crate::leanh::LeanObject,
    mut v_b_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
    mut v___y_2123_: *mut crate::leanh::LeanObject,
    mut v___y_2124_: *mut crate::leanh::LeanObject,
    mut v___y_2125_: *mut crate::leanh::LeanObject,
    mut v___y_2126_: *mut crate::leanh::LeanObject,
    mut v___y_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2129_: usize = 0;
    let mut v_i_boxed_2130_: usize = 0;
    let mut v_res_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2129_ = crate::leanh::lean_unbox_usize(v_sz_2119_);
    crate::leanh::lean_dec(v_sz_2119_);
    v_i_boxed_2130_ = crate::leanh::lean_unbox_usize(v_i_2120_);
    crate::leanh::lean_dec(v_i_2120_);
    v_res_2131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(v___x_2117_, v_as_2118_, v_sz_boxed_2129_, v_i_boxed_2130_, v_b_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
    crate::leanh::lean_dec_ref(v___y_2126_);
    crate::leanh::lean_dec(v___y_2125_);
    crate::leanh::lean_dec(v___y_2124_);
    crate::leanh::lean_dec(v___y_2123_);
    crate::leanh::lean_dec_ref(v_as_2118_);
    return v_res_2131_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(
    mut v_a_2132_: *mut crate::leanh::LeanObject,
    mut v_as_2133_: *mut crate::leanh::LeanObject,
    mut v_sz_2134_: usize,
    mut v_i_2135_: usize,
    mut v_b_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v_a_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2144_ = lean_usize_dec_lt(v_i_2135_, v_sz_2134_);
                if v___x_2144_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2137_);
                    crate::leanh::lean_dec_ref(v_a_2132_);
                    v___x_2145_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2145_, 0, v_b_2136_);
                    crate::leanh::lean_ctor_set(v___x_2145_, 1, v___y_2142_);
                    return v___x_2145_;
                } else {
                    v_a_2146_ = lean_array_uget_borrowed(v_as_2133_, v_i_2135_);
                    crate::leanh::lean_inc_ref(v___y_2137_);
                    crate::leanh::lean_inc_ref(v_a_2132_);
                    crate::leanh::lean_inc(v_a_2146_);
                    v___x_2147_ = l_Lake_ModuleFacet_fetch___redArg(
                        v_a_2146_,
                        v_a_2132_,
                        v___y_2137_,
                        v___y_2138_,
                        v___y_2139_,
                        v___y_2140_,
                        v___y_2141_,
                        v___y_2142_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2147_) == 0 {
                        v_a_2148_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                        crate::leanh::lean_inc(v_a_2148_);
                        v_a_2149_ = crate::leanh::lean_ctor_get(v___x_2147_, 1);
                        crate::leanh::lean_inc(v_a_2149_);
                        crate::leanh::lean_dec_ref_known(v___x_2147_, 2);
                        v___x_2150_ = lean_array_push(v_b_2136_, v_a_2148_);
                        v___x_2151_ = 1usize;
                        v___x_2152_ = lean_usize_add(v_i_2135_, v___x_2151_);
                        v_i_2135_ = v___x_2152_;
                        v_b_2136_ = v___x_2150_;
                        v___y_2142_ = v_a_2149_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2137_);
                        crate::leanh::lean_dec_ref(v_b_2136_);
                        crate::leanh::lean_dec_ref(v_a_2132_);
                        v_a_2154_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                        v_a_2155_ = crate::leanh::lean_ctor_get(v___x_2147_, 1);
                        v_isSharedCheck_2162_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2162_ == 0 {
                            v___x_2157_ = v___x_2147_;
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2155_);
                            crate::leanh::lean_inc(v_a_2154_);
                            crate::leanh::lean_dec(v___x_2147_);
                            v___x_2157_ = crate::leanh::lean_box(0);
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2158_ == 0 {
                    v___x_2160_ = v___x_2157_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2161_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2155_);
                    v___x_2160_ = v_reuseFailAlloc_2161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7___boxed(
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v_as_2164_: *mut crate::leanh::LeanObject,
    mut v_sz_2165_: *mut crate::leanh::LeanObject,
    mut v_i_2166_: *mut crate::leanh::LeanObject,
    mut v_b_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
    mut v___y_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2175_: usize = 0;
    let mut v_i_boxed_2176_: usize = 0;
    let mut v_res_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2175_ = crate::leanh::lean_unbox_usize(v_sz_2165_);
    crate::leanh::lean_dec(v_sz_2165_);
    v_i_boxed_2176_ = crate::leanh::lean_unbox_usize(v_i_2166_);
    crate::leanh::lean_dec(v_i_2166_);
    v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(v_a_2163_, v_as_2164_, v_sz_boxed_2175_, v_i_boxed_2176_, v_b_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
    crate::leanh::lean_dec_ref(v___y_2172_);
    crate::leanh::lean_dec(v___y_2171_);
    crate::leanh::lean_dec(v___y_2170_);
    crate::leanh::lean_dec(v___y_2169_);
    crate::leanh::lean_dec_ref(v_as_2164_);
    return v_res_2177_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(
    mut v_shouldExport_2178_: u8,
    mut v_as_2179_: *mut crate::leanh::LeanObject,
    mut v_sz_2180_: usize,
    mut v_i_2181_: usize,
    mut v_b_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lib_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2198_: usize = 0;
    let mut v___x_2199_: usize = 0;
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2190_ = lean_usize_dec_lt(v_i_2181_, v_sz_2180_);
                if v___x_2190_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2183_);
                    v___x_2191_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2191_, 0, v_b_2182_);
                    crate::leanh::lean_ctor_set(v___x_2191_, 1, v___y_2188_);
                    return v___x_2191_;
                } else {
                    v_a_2192_ = lean_array_uget_borrowed(v_as_2179_, v_i_2181_);
                    v_lib_2193_ = crate::leanh::lean_ctor_get(v_a_2192_, 0);
                    v_config_2194_ = crate::leanh::lean_ctor_get(v_lib_2193_, 2);
                    v_nativeFacets_2195_ = crate::leanh::lean_ctor_get(v_config_2194_, 8);
                    v___x_2196_ = crate::leanh::lean_box((v_shouldExport_2178_) as usize);
                    crate::leanh::lean_inc_ref(v_nativeFacets_2195_);
                    v___x_2197_ = crate::leanh::lean_apply_1(v_nativeFacets_2195_, v___x_2196_);
                    v_sz_2198_ = lean_array_size(v___x_2197_);
                    v___x_2199_ = 0usize;
                    crate::leanh::lean_inc_ref(v___y_2183_);
                    crate::leanh::lean_inc(v_a_2192_);
                    v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(v_a_2192_, v___x_2197_, v_sz_2198_, v___x_2199_, v_b_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
                    crate::leanh::lean_dec_ref(v___x_2197_);
                    if crate::leanh::lean_obj_tag(v___x_2200_) == 0 {
                        v_a_2201_ = crate::leanh::lean_ctor_get(v___x_2200_, 0);
                        crate::leanh::lean_inc(v_a_2201_);
                        v_a_2202_ = crate::leanh::lean_ctor_get(v___x_2200_, 1);
                        crate::leanh::lean_inc(v_a_2202_);
                        crate::leanh::lean_dec_ref_known(v___x_2200_, 2);
                        v___x_2203_ = 1usize;
                        v___x_2204_ = lean_usize_add(v_i_2181_, v___x_2203_);
                        v_i_2181_ = v___x_2204_;
                        v_b_2182_ = v_a_2201_;
                        v___y_2188_ = v_a_2202_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2183_);
                        return v___x_2200_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8___boxed(
    mut v_shouldExport_2206_: *mut crate::leanh::LeanObject,
    mut v_as_2207_: *mut crate::leanh::LeanObject,
    mut v_sz_2208_: *mut crate::leanh::LeanObject,
    mut v_i_2209_: *mut crate::leanh::LeanObject,
    mut v_b_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
    mut v___y_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_shouldExport_boxed_2218_: u8 = 0;
    let mut v_sz_boxed_2219_: usize = 0;
    let mut v_i_boxed_2220_: usize = 0;
    let mut v_res_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_2218_ = (crate::leanh::lean_unbox(v_shouldExport_2206_) as u8);
    v_sz_boxed_2219_ = crate::leanh::lean_unbox_usize(v_sz_2208_);
    crate::leanh::lean_dec(v_sz_2208_);
    v_i_boxed_2220_ = crate::leanh::lean_unbox_usize(v_i_2209_);
    crate::leanh::lean_dec(v_i_2209_);
    v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(v_shouldExport_boxed_2218_, v_as_2207_, v_sz_boxed_2219_, v_i_boxed_2220_, v_b_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
    crate::leanh::lean_dec_ref(v___y_2215_);
    crate::leanh::lean_dec(v___y_2214_);
    crate::leanh::lean_dec(v___y_2213_);
    crate::leanh::lean_dec(v___y_2212_);
    crate::leanh::lean_dec_ref(v_as_2207_);
    return v_res_2221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(
    mut v_a_2222_: *mut crate::leanh::LeanObject,
    mut v_as_2223_: *mut crate::leanh::LeanObject,
    mut v_i_2224_: usize,
    mut v_stop_2225_: usize,
    mut v_b_2226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: usize = 0;
    let mut v___x_2230_: usize = 0;
    let mut v___x_2232_: u8 = 0;
    let mut v_toConfigDecl_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2232_ = lean_usize_dec_eq(v_i_2224_, v_stop_2225_);
                if v___x_2232_ == 0 {
                    v_toConfigDecl_2233_ = lean_array_uget_borrowed(v_as_2223_, v_i_2224_);
                    v_name_2234_ = crate::leanh::lean_ctor_get(v_toConfigDecl_2233_, 1);
                    v_kind_2235_ = crate::leanh::lean_ctor_get(v_toConfigDecl_2233_, 2);
                    v_config_2236_ = crate::leanh::lean_ctor_get(v_toConfigDecl_2233_, 3);
                    v___x_2237_ = l_Lake_ExternLib_keyword;
                    v___x_2238_ = lean_name_eq(v_kind_2235_, v___x_2237_);
                    if v___x_2238_ == 0 {
                        v___y_2228_ = v_b_2226_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_config_2236_);
                        crate::leanh::lean_inc(v_name_2234_);
                        crate::leanh::lean_inc_ref(v_a_2222_);
                        v___x_2239_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2239_, 0, v_a_2222_);
                        crate::leanh::lean_ctor_set(v___x_2239_, 1, v_name_2234_);
                        crate::leanh::lean_ctor_set(v___x_2239_, 2, v_config_2236_);
                        v___x_2240_ = lean_array_push(v_b_2226_, v___x_2239_);
                        v___y_2228_ = v___x_2240_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2222_);
                    return v_b_2226_;
                }
            }
            1 => {
                v___x_2229_ = 1usize;
                v___x_2230_ = lean_usize_add(v_i_2224_, v___x_2229_);
                v_i_2224_ = v___x_2230_;
                v_b_2226_ = v___y_2228_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2___boxed(
    mut v_a_2241_: *mut crate::leanh::LeanObject,
    mut v_as_2242_: *mut crate::leanh::LeanObject,
    mut v_i_2243_: *mut crate::leanh::LeanObject,
    mut v_stop_2244_: *mut crate::leanh::LeanObject,
    mut v_b_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2246_: usize = 0;
    let mut v_stop_boxed_2247_: usize = 0;
    let mut v_res_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2246_ = crate::leanh::lean_unbox_usize(v_i_2243_);
    crate::leanh::lean_dec(v_i_2243_);
    v_stop_boxed_2247_ = crate::leanh::lean_unbox_usize(v_stop_2244_);
    crate::leanh::lean_dec(v_stop_2244_);
    v_res_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(v_a_2241_, v_as_2242_, v_i_boxed_2246_, v_stop_boxed_2247_, v_b_2245_);
    crate::leanh::lean_dec_ref(v_as_2242_);
    return v_res_2248_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(
    mut v_as_2249_: *mut crate::leanh::LeanObject,
    mut v_sz_2250_: usize,
    mut v_i_2251_: usize,
    mut v_b_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: usize = 0;
    let mut v___x_2275_: usize = 0;
    let mut v_a_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2260_ = lean_usize_dec_lt(v_i_2251_, v_sz_2250_);
                if v___x_2260_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2253_);
                    v___x_2261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2261_, 0, v_b_2252_);
                    crate::leanh::lean_ctor_set(v___x_2261_, 1, v___y_2258_);
                    return v___x_2261_;
                } else {
                    v_a_2262_ = lean_array_uget_borrowed(v_as_2249_, v_i_2251_);
                    v_pkg_2263_ = crate::leanh::lean_ctor_get(v_a_2262_, 0);
                    v_name_2264_ = crate::leanh::lean_ctor_get(v_a_2262_, 1);
                    v_keyName_2265_ = crate::leanh::lean_ctor_get(v_pkg_2263_, 2);
                    v___x_2266_ = l_Lake_ExternLib_staticFacet;
                    crate::leanh::lean_inc(v_name_2264_);
                    crate::leanh::lean_inc(v_keyName_2265_);
                    v___x_2267_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2267_, 0, v_keyName_2265_);
                    crate::leanh::lean_ctor_set(v___x_2267_, 1, v_name_2264_);
                    v___x_2268_ = l_Lake_ExternLib_keyword;
                    crate::leanh::lean_inc(v_a_2262_);
                    v___x_2269_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2269_, 0, v___x_2267_);
                    crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2268_);
                    crate::leanh::lean_ctor_set(v___x_2269_, 2, v_a_2262_);
                    crate::leanh::lean_ctor_set(v___x_2269_, 3, v___x_2266_);
                    crate::leanh::lean_inc_ref(v___y_2253_);
                    crate::leanh::lean_inc_ref(v___y_2257_);
                    crate::leanh::lean_inc(v___y_2256_);
                    crate::leanh::lean_inc(v___y_2255_);
                    crate::leanh::lean_inc(v___y_2254_);
                    v___x_2270_ = crate::leanh::lean_apply_7(
                        v___y_2253_,
                        v___x_2269_,
                        v___y_2254_,
                        v___y_2255_,
                        v___y_2256_,
                        v___y_2257_,
                        v___y_2258_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2270_) == 0 {
                        v_a_2271_ = crate::leanh::lean_ctor_get(v___x_2270_, 0);
                        crate::leanh::lean_inc(v_a_2271_);
                        v_a_2272_ = crate::leanh::lean_ctor_get(v___x_2270_, 1);
                        crate::leanh::lean_inc(v_a_2272_);
                        crate::leanh::lean_dec_ref_known(v___x_2270_, 2);
                        v___x_2273_ = lean_array_push(v_b_2252_, v_a_2271_);
                        v___x_2274_ = 1usize;
                        v___x_2275_ = lean_usize_add(v_i_2251_, v___x_2274_);
                        v_i_2251_ = v___x_2275_;
                        v_b_2252_ = v___x_2273_;
                        v___y_2258_ = v_a_2272_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2253_);
                        crate::leanh::lean_dec_ref(v_b_2252_);
                        v_a_2277_ = crate::leanh::lean_ctor_get(v___x_2270_, 0);
                        v_a_2278_ = crate::leanh::lean_ctor_get(v___x_2270_, 1);
                        v_isSharedCheck_2285_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2270_)) as u8;
                        if v_isSharedCheck_2285_ == 0 {
                            v___x_2280_ = v___x_2270_;
                            v_isShared_2281_ = v_isSharedCheck_2285_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2278_);
                            crate::leanh::lean_inc(v_a_2277_);
                            crate::leanh::lean_dec(v___x_2270_);
                            v___x_2280_ = crate::leanh::lean_box(0);
                            v_isShared_2281_ = v_isSharedCheck_2285_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2281_ == 0 {
                    v___x_2283_ = v___x_2280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_a_2278_);
                    v___x_2283_ = v_reuseFailAlloc_2284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1___boxed(
    mut v_as_2286_: *mut crate::leanh::LeanObject,
    mut v_sz_2287_: *mut crate::leanh::LeanObject,
    mut v_i_2288_: *mut crate::leanh::LeanObject,
    mut v_b_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2297_: usize = 0;
    let mut v_i_boxed_2298_: usize = 0;
    let mut v_res_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2297_ = crate::leanh::lean_unbox_usize(v_sz_2287_);
    crate::leanh::lean_dec(v_sz_2287_);
    v_i_boxed_2298_ = crate::leanh::lean_unbox_usize(v_i_2288_);
    crate::leanh::lean_dec(v_i_2288_);
    v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v_as_2286_, v_sz_boxed_2297_, v_i_boxed_2298_, v_b_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
    crate::leanh::lean_dec_ref(v___y_2294_);
    crate::leanh::lean_dec(v___y_2293_);
    crate::leanh::lean_dec(v___y_2292_);
    crate::leanh::lean_dec(v___y_2291_);
    crate::leanh::lean_dec_ref(v_as_2286_);
    return v_res_2299_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(
    mut v_as_2302_: *mut crate::leanh::LeanObject,
    mut v_sz_2303_: usize,
    mut v_i_2304_: usize,
    mut v_b_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: usize = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: usize = 0;
    let mut v___x_2333_: usize = 0;
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: usize = 0;
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2323_ = lean_usize_dec_lt(v_i_2304_, v_sz_2303_);
                if v___x_2323_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2306_);
                    v___x_2324_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2324_, 0, v_b_2305_);
                    crate::leanh::lean_ctor_set(v___x_2324_, 1, v___y_2311_);
                    return v___x_2324_;
                } else {
                    v_a_2325_ = lean_array_uget_borrowed(v_as_2302_, v_i_2304_);
                    v_targetDecls_2326_ = crate::leanh::lean_ctor_get(v_a_2325_, 14);
                    v___x_2327_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0;
                    v___x_2329_ = lean_array_get_size(v_targetDecls_2326_);
                    v___x_2330_ = lean_nat_dec_lt(v___x_2327_, v___x_2329_);
                    if v___x_2330_ == 0 {
                        v___y_2314_ = v___x_2328_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2331_ = lean_nat_dec_le(v___x_2329_, v___x_2329_);
                        if v___x_2331_ == 0 {
                            if v___x_2330_ == 0 {
                                v___y_2314_ = v___x_2328_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2332_ = 0usize;
                                v___x_2333_ = lean_usize_of_nat(v___x_2329_);
                                crate::leanh::lean_inc(v_a_2325_);
                                v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(v_a_2325_, v_targetDecls_2326_, v___x_2332_, v___x_2333_, v___x_2328_);
                                v___y_2314_ = v___x_2334_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2335_ = 0usize;
                            v___x_2336_ = lean_usize_of_nat(v___x_2329_);
                            crate::leanh::lean_inc(v_a_2325_);
                            v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(v_a_2325_, v_targetDecls_2326_, v___x_2335_, v___x_2336_, v___x_2328_);
                            v___y_2314_ = v___x_2337_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_2315_ = lean_array_size(v___y_2314_);
                v___x_2316_ = 0usize;
                crate::leanh::lean_inc_ref(v___y_2306_);
                v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___y_2314_, v_sz_2315_, v___x_2316_, v_b_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
                crate::leanh::lean_dec_ref(v___y_2314_);
                if crate::leanh::lean_obj_tag(v___x_2317_) == 0 {
                    v_a_2318_ = crate::leanh::lean_ctor_get(v___x_2317_, 0);
                    crate::leanh::lean_inc(v_a_2318_);
                    v_a_2319_ = crate::leanh::lean_ctor_get(v___x_2317_, 1);
                    crate::leanh::lean_inc(v_a_2319_);
                    crate::leanh::lean_dec_ref_known(v___x_2317_, 2);
                    v___x_2320_ = 1usize;
                    v___x_2321_ = lean_usize_add(v_i_2304_, v___x_2320_);
                    v_i_2304_ = v___x_2321_;
                    v_b_2305_ = v_a_2318_;
                    v___y_2311_ = v_a_2319_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2306_);
                    return v___x_2317_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___boxed(
    mut v_as_2338_: *mut crate::leanh::LeanObject,
    mut v_sz_2339_: *mut crate::leanh::LeanObject,
    mut v_i_2340_: *mut crate::leanh::LeanObject,
    mut v_b_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2349_: usize = 0;
    let mut v_i_boxed_2350_: usize = 0;
    let mut v_res_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2349_ = crate::leanh::lean_unbox_usize(v_sz_2339_);
    crate::leanh::lean_dec(v_sz_2339_);
    v_i_boxed_2350_ = crate::leanh::lean_unbox_usize(v_i_2340_);
    crate::leanh::lean_dec(v_i_2340_);
    v_res_2351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(v_as_2338_, v_sz_boxed_2349_, v_i_boxed_2350_, v_b_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
    crate::leanh::lean_dec_ref(v___y_2346_);
    crate::leanh::lean_dec(v___y_2345_);
    crate::leanh::lean_dec(v___y_2344_);
    crate::leanh::lean_dec(v___y_2343_);
    crate::leanh::lean_dec_ref(v_as_2338_);
    return v_res_2351_;
}
pub unsafe fn _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ =
        l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0;
    v___x_2354_ = l_Lake_BuildTrace_nil(v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(
    mut v___x_2357_: *mut crate::leanh::LeanObject,
    mut v___x_2358_: *mut crate::leanh::LeanObject,
    mut v_sz_2359_: usize,
    mut v___x_2360_: usize,
    mut v_objJobs_2361_: *mut crate::leanh::LeanObject,
    mut v___x_2362_: *mut crate::leanh::LeanObject,
    mut v_pkg_2363_: *mut crate::leanh::LeanObject,
    mut v_root_2364_: *mut crate::leanh::LeanObject,
    mut v_supportInterpreter_2365_: u8,
    mut v_toLeanConfig_2366_: *mut crate::leanh::LeanObject,
    mut v_libJobs_2367_: *mut crate::leanh::LeanObject,
    mut v_exeName_2368_: *mut crate::leanh::LeanObject,
    mut v_self_2369_: *mut crate::leanh::LeanObject,
    mut v___x_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2393_: u8 = 0;
    let mut v_task_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2397_: usize = 0;
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2404_: usize = 0;
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toArray_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2416_: usize = 0;
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2422_: usize = 0;
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2437_: usize = 0;
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v_buildDir_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2464_: u8 = 0;
    let mut v_a_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v_a_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2482_: u8 = 0;
    let mut v_a_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_a_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2496_: u8 = 0;
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v_a_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut v_reuseFailAlloc_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2511_: u8 = 0;
    let mut v_unused_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: u8 = 0;
    let mut v___x_2516_: u8 = 0;
    let mut v___x_2517_: usize = 0;
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_a_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u8 = 0;
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2552_: u8 = 0;
    let mut v_a_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2557_: u8 = 0;
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut v_a_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___y_2371_);
                crate::leanh::lean_inc_ref(v___x_2357_);
                v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(v___x_2357_, v___x_2358_, v_sz_2359_, v___x_2360_, v_objJobs_2361_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
                if crate::leanh::lean_obj_tag(v___x_2378_) == 0 {
                    v_a_2379_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                    crate::leanh::lean_inc(v_a_2379_);
                    v_a_2380_ = crate::leanh::lean_ctor_get(v___x_2378_, 1);
                    crate::leanh::lean_inc(v_a_2380_);
                    crate::leanh::lean_dec_ref_known(v___x_2378_, 2);
                    v_keyName_2381_ = crate::leanh::lean_ctor_get(v_pkg_2363_, 2);
                    v_dir_2382_ = crate::leanh::lean_ctor_get(v_pkg_2363_, 4);
                    crate::leanh::lean_inc_ref(v_dir_2382_);
                    v_config_2383_ = crate::leanh::lean_ctor_get(v_pkg_2363_, 6);
                    crate::leanh::lean_inc_ref(v_config_2383_);
                    v___x_2384_ = l_Lake_Module_transImportsFacet;
                    crate::leanh::lean_inc(v_root_2364_);
                    crate::leanh::lean_inc(v_keyName_2381_);
                    v___x_2385_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2385_, 0, v_keyName_2381_);
                    crate::leanh::lean_ctor_set(v___x_2385_, 1, v_root_2364_);
                    v___x_2386_ = l_Lake_Module_keyword;
                    v___x_2387_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2387_, 0, v___x_2385_);
                    crate::leanh::lean_ctor_set(v___x_2387_, 1, v___x_2386_);
                    crate::leanh::lean_ctor_set(v___x_2387_, 2, v___x_2357_);
                    crate::leanh::lean_ctor_set(v___x_2387_, 3, v___x_2384_);
                    crate::leanh::lean_inc_ref(v___y_2371_);
                    crate::leanh::lean_inc_ref(v___y_2375_);
                    crate::leanh::lean_inc(v___y_2374_);
                    crate::leanh::lean_inc(v___y_2373_);
                    crate::leanh::lean_inc(v___x_2362_);
                    v___x_2388_ = crate::leanh::lean_apply_7(
                        v___y_2371_,
                        v___x_2387_,
                        v___x_2362_,
                        v___y_2373_,
                        v___y_2374_,
                        v___y_2375_,
                        v_a_2380_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2388_) == 0 {
                        v_a_2389_ = crate::leanh::lean_ctor_get(v___x_2388_, 0);
                        v_a_2390_ = crate::leanh::lean_ctor_get(v___x_2388_, 1);
                        v_isSharedCheck_2552_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2388_)) as u8;
                        if v_isSharedCheck_2552_ == 0 {
                            v___x_2392_ = v___x_2388_;
                            v_isShared_2393_ = v_isSharedCheck_2552_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2390_);
                            crate::leanh::lean_inc(v_a_2389_);
                            crate::leanh::lean_dec(v___x_2388_);
                            v___x_2392_ = crate::leanh::lean_box(0);
                            v_isShared_2393_ = v_isSharedCheck_2552_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_config_2383_);
                        crate::leanh::lean_dec_ref(v_dir_2382_);
                        crate::leanh::lean_dec(v_a_2379_);
                        crate::leanh::lean_dec_ref(v___y_2371_);
                        crate::leanh::lean_dec_ref(v_self_2369_);
                        crate::leanh::lean_dec_ref(v_exeName_2368_);
                        crate::leanh::lean_dec_ref(v_libJobs_2367_);
                        crate::leanh::lean_dec(v_root_2364_);
                        crate::leanh::lean_dec_ref(v_pkg_2363_);
                        crate::leanh::lean_dec(v___x_2362_);
                        v_a_2553_ = crate::leanh::lean_ctor_get(v___x_2388_, 0);
                        v_a_2554_ = crate::leanh::lean_ctor_get(v___x_2388_, 1);
                        v_isSharedCheck_2561_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2388_)) as u8;
                        if v_isSharedCheck_2561_ == 0 {
                            v___x_2556_ = v___x_2388_;
                            v_isShared_2557_ = v_isSharedCheck_2561_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2554_);
                            crate::leanh::lean_inc(v_a_2553_);
                            crate::leanh::lean_dec(v___x_2388_);
                            v___x_2556_ = crate::leanh::lean_box(0);
                            v_isShared_2557_ = v_isSharedCheck_2561_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2371_);
                    crate::leanh::lean_dec_ref(v_self_2369_);
                    crate::leanh::lean_dec_ref(v_exeName_2368_);
                    crate::leanh::lean_dec_ref(v_libJobs_2367_);
                    crate::leanh::lean_dec(v_root_2364_);
                    crate::leanh::lean_dec_ref(v_pkg_2363_);
                    crate::leanh::lean_dec(v___x_2362_);
                    crate::leanh::lean_dec_ref(v___x_2357_);
                    v_a_2562_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                    v_a_2563_ = crate::leanh::lean_ctor_get(v___x_2378_, 1);
                    v_isSharedCheck_2570_ = (!crate::leanh::lean_is_exclusive(v___x_2378_)) as u8;
                    if v_isSharedCheck_2570_ == 0 {
                        v___x_2565_ = v___x_2378_;
                        v_isShared_2566_ = v_isSharedCheck_2570_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2563_);
                        crate::leanh::lean_inc(v_a_2562_);
                        crate::leanh::lean_dec(v___x_2378_);
                        v___x_2565_ = crate::leanh::lean_box(0);
                        v_isShared_2566_ = v_isSharedCheck_2570_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v_task_2394_ = crate::leanh::lean_ctor_get(v_a_2389_, 0);
                crate::leanh::lean_inc_ref(v_task_2394_);
                crate::leanh::lean_dec(v_a_2389_);
                v___x_2395_ = lean_io_wait(v_task_2394_);
                if crate::leanh::lean_obj_tag(v___x_2395_) == 0 {
                    crate::leanh::lean_del_object(v___x_2392_);
                    crate::leanh::lean_dec(v_root_2364_);
                    v_a_2396_ = crate::leanh::lean_ctor_get(v___x_2395_, 0);
                    crate::leanh::lean_inc(v_a_2396_);
                    crate::leanh::lean_dec_ref_known(v___x_2395_, 2);
                    v_sz_2397_ = lean_array_size(v_a_2396_);
                    crate::leanh::lean_inc_ref(v___y_2371_);
                    v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(v_supportInterpreter_2365_, v_a_2396_, v_sz_2397_, v___x_2360_, v_a_2379_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2390_);
                    if crate::leanh::lean_obj_tag(v___x_2398_) == 0 {
                        v_a_2399_ = crate::leanh::lean_ctor_get(v___x_2398_, 0);
                        crate::leanh::lean_inc(v_a_2399_);
                        v_a_2400_ = crate::leanh::lean_ctor_get(v___x_2398_, 1);
                        crate::leanh::lean_inc(v_a_2400_);
                        crate::leanh::lean_dec_ref_known(v___x_2398_, 2);
                        v_moreLinkObjs_2401_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2366_, 6);
                        v_moreLinkLibs_2402_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2366_, 7);
                        v_weakLinkArgs_2403_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2366_, 9);
                        v_sz_2404_ = lean_array_size(v_moreLinkObjs_2401_);
                        crate::leanh::lean_inc_ref(v___y_2371_);
                        crate::leanh::lean_inc_ref(v_pkg_2363_);
                        v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(v_pkg_2363_, v_moreLinkObjs_2401_, v_sz_2404_, v___x_2360_, v_a_2399_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2400_);
                        if crate::leanh::lean_obj_tag(v___x_2405_) == 0 {
                            v_a_2406_ = crate::leanh::lean_ctor_get(v___x_2405_, 0);
                            crate::leanh::lean_inc(v_a_2406_);
                            v_a_2407_ = crate::leanh::lean_ctor_get(v___x_2405_, 1);
                            crate::leanh::lean_inc(v_a_2407_);
                            crate::leanh::lean_dec_ref_known(v___x_2405_, 2);
                            v___x_2513_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13;
                            v___x_2514_ = lean_array_get_size(v_a_2396_);
                            v___x_2515_ = lean_nat_dec_lt(v___x_2370_, v___x_2514_);
                            if v___x_2515_ == 0 {
                                crate::leanh::lean_dec(v_a_2396_);
                                v___y_2409_ = v___x_2513_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2516_ = lean_nat_dec_le(v___x_2514_, v___x_2514_);
                                if v___x_2516_ == 0 {
                                    if v___x_2515_ == 0 {
                                        crate::leanh::lean_dec(v_a_2396_);
                                        v___y_2409_ = v___x_2513_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_2517_ = lean_usize_of_nat(v___x_2514_);
                                        v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(v_a_2396_, v___x_2360_, v___x_2517_, v___x_2513_);
                                        crate::leanh::lean_dec(v_a_2396_);
                                        v___y_2409_ = v___x_2518_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___x_2519_ = lean_usize_of_nat(v___x_2514_);
                                    v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(v_a_2396_, v___x_2360_, v___x_2519_, v___x_2513_);
                                    crate::leanh::lean_dec(v_a_2396_);
                                    v___y_2409_ = v___x_2520_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2396_);
                            crate::leanh::lean_dec_ref(v_config_2383_);
                            crate::leanh::lean_dec_ref(v_dir_2382_);
                            crate::leanh::lean_dec_ref(v___y_2371_);
                            crate::leanh::lean_dec_ref(v_self_2369_);
                            crate::leanh::lean_dec_ref(v_exeName_2368_);
                            crate::leanh::lean_dec_ref(v_libJobs_2367_);
                            crate::leanh::lean_dec_ref(v_pkg_2363_);
                            crate::leanh::lean_dec(v___x_2362_);
                            v_a_2521_ = crate::leanh::lean_ctor_get(v___x_2405_, 0);
                            v_a_2522_ = crate::leanh::lean_ctor_get(v___x_2405_, 1);
                            v_isSharedCheck_2529_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2405_)) as u8;
                            if v_isSharedCheck_2529_ == 0 {
                                v___x_2524_ = v___x_2405_;
                                v_isShared_2525_ = v_isSharedCheck_2529_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2522_);
                                crate::leanh::lean_inc(v_a_2521_);
                                crate::leanh::lean_dec(v___x_2405_);
                                v___x_2524_ = crate::leanh::lean_box(0);
                                v_isShared_2525_ = v_isSharedCheck_2529_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2396_);
                        crate::leanh::lean_dec_ref(v_config_2383_);
                        crate::leanh::lean_dec_ref(v_dir_2382_);
                        crate::leanh::lean_dec_ref(v___y_2371_);
                        crate::leanh::lean_dec_ref(v_self_2369_);
                        crate::leanh::lean_dec_ref(v_exeName_2368_);
                        crate::leanh::lean_dec_ref(v_libJobs_2367_);
                        crate::leanh::lean_dec_ref(v_pkg_2363_);
                        crate::leanh::lean_dec(v___x_2362_);
                        v_a_2530_ = crate::leanh::lean_ctor_get(v___x_2398_, 0);
                        v_a_2531_ = crate::leanh::lean_ctor_get(v___x_2398_, 1);
                        v_isSharedCheck_2538_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2398_)) as u8;
                        if v_isSharedCheck_2538_ == 0 {
                            v___x_2533_ = v___x_2398_;
                            v_isShared_2534_ = v_isSharedCheck_2538_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2531_);
                            crate::leanh::lean_inc(v_a_2530_);
                            crate::leanh::lean_dec(v___x_2398_);
                            v___x_2533_ = crate::leanh::lean_box(0);
                            v_isShared_2534_ = v_isSharedCheck_2538_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2395_);
                    crate::leanh::lean_dec_ref(v_config_2383_);
                    crate::leanh::lean_dec_ref(v_dir_2382_);
                    crate::leanh::lean_dec(v_a_2379_);
                    crate::leanh::lean_dec_ref(v___y_2371_);
                    crate::leanh::lean_dec_ref(v_self_2369_);
                    crate::leanh::lean_dec_ref(v_exeName_2368_);
                    crate::leanh::lean_dec_ref(v_libJobs_2367_);
                    crate::leanh::lean_dec_ref(v_pkg_2363_);
                    crate::leanh::lean_dec(v___x_2362_);
                    v___x_2539_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2;
                    v___x_2540_ = 1;
                    v___x_2541_ = l_Lean_Name_toString(v_root_2364_, v___x_2540_);
                    v___x_2542_ = lean_string_append(v___x_2539_, v___x_2541_);
                    crate::leanh::lean_dec_ref(v___x_2541_);
                    v___x_2543_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3;
                    v___x_2544_ = lean_string_append(v___x_2542_, v___x_2543_);
                    v___x_2545_ = 3;
                    v___x_2546_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2544_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2546_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2545_,
                    );
                    v___x_2547_ = lean_array_get_size(v_a_2390_);
                    v___x_2548_ = lean_array_push(v_a_2390_, v___x_2546_);
                    if v_isShared_2393_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2392_, 1);
                        crate::leanh::lean_ctor_set(v___x_2392_, 1, v___x_2548_);
                        crate::leanh::lean_ctor_set(v___x_2392_, 0, v___x_2547_);
                        v___x_2550_ = v___x_2392_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2551_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2547_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2548_);
                        v___x_2550_ = v_reuseFailAlloc_2551_;
                        state = 21;
                        continue;
                    }
                }
            }
            2 => {
                v_toArray_2410_ = crate::leanh::lean_ctor_get(v___y_2409_, 1);
                v_isSharedCheck_2511_ = (!crate::leanh::lean_is_exclusive(v___y_2409_)) as u8;
                if v_isSharedCheck_2511_ == 0 {
                    v_unused_2512_ = crate::leanh::lean_ctor_get(v___y_2409_, 0);
                    crate::leanh::lean_dec(v_unused_2512_);
                    v___x_2412_ = v___y_2409_;
                    v_isShared_2413_ = v_isSharedCheck_2511_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toArray_2410_);
                    crate::leanh::lean_dec(v___y_2409_);
                    v___x_2412_ = crate::leanh::lean_box(0);
                    v_isShared_2413_ = v_isSharedCheck_2511_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2412_, 1, v_libJobs_2367_);
                    crate::leanh::lean_ctor_set(v___x_2412_, 0, v_a_2406_);
                    v___x_2415_ = v___x_2412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_libJobs_2367_);
                    v___x_2415_ = v_reuseFailAlloc_2510_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_2416_ = lean_array_size(v_toArray_2410_);
                crate::leanh::lean_inc_ref(v___y_2371_);
                v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(v_toArray_2410_, v_sz_2416_, v___x_2360_, v___x_2415_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2407_);
                crate::leanh::lean_dec_ref(v_toArray_2410_);
                if crate::leanh::lean_obj_tag(v___x_2417_) == 0 {
                    v_a_2418_ = crate::leanh::lean_ctor_get(v___x_2417_, 0);
                    crate::leanh::lean_inc(v_a_2418_);
                    v_a_2419_ = crate::leanh::lean_ctor_get(v___x_2417_, 1);
                    crate::leanh::lean_inc(v_a_2419_);
                    crate::leanh::lean_dec_ref_known(v___x_2417_, 2);
                    v_fst_2420_ = crate::leanh::lean_ctor_get(v_a_2418_, 0);
                    crate::leanh::lean_inc(v_fst_2420_);
                    v_snd_2421_ = crate::leanh::lean_ctor_get(v_a_2418_, 1);
                    crate::leanh::lean_inc(v_snd_2421_);
                    crate::leanh::lean_dec(v_a_2418_);
                    v_sz_2422_ = lean_array_size(v_moreLinkLibs_2402_);
                    crate::leanh::lean_inc_ref(v___y_2371_);
                    crate::leanh::lean_inc_ref(v_pkg_2363_);
                    v___x_2423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(v_pkg_2363_, v_moreLinkLibs_2402_, v_sz_2422_, v___x_2360_, v_snd_2421_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2419_);
                    if crate::leanh::lean_obj_tag(v___x_2423_) == 0 {
                        v_a_2424_ = crate::leanh::lean_ctor_get(v___x_2423_, 0);
                        crate::leanh::lean_inc(v_a_2424_);
                        v_a_2425_ = crate::leanh::lean_ctor_get(v___x_2423_, 1);
                        crate::leanh::lean_inc(v_a_2425_);
                        crate::leanh::lean_dec_ref_known(v___x_2423_, 2);
                        v___x_2426_ = l_Lake_Package_transDepsFacet;
                        crate::leanh::lean_inc(v_keyName_2381_);
                        v___x_2427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2427_, 0, v_keyName_2381_);
                        v___x_2428_ = l_Lake_Package_keyword;
                        crate::leanh::lean_inc_ref(v_pkg_2363_);
                        v___x_2429_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2429_, 0, v___x_2427_);
                        crate::leanh::lean_ctor_set(v___x_2429_, 1, v___x_2428_);
                        crate::leanh::lean_ctor_set(v___x_2429_, 2, v_pkg_2363_);
                        crate::leanh::lean_ctor_set(v___x_2429_, 3, v___x_2426_);
                        crate::leanh::lean_inc_ref(v___y_2371_);
                        crate::leanh::lean_inc_ref(v___y_2375_);
                        crate::leanh::lean_inc(v___y_2374_);
                        crate::leanh::lean_inc(v___y_2373_);
                        crate::leanh::lean_inc(v___x_2362_);
                        v___x_2430_ = crate::leanh::lean_apply_7(
                            v___y_2371_,
                            v___x_2429_,
                            v___x_2362_,
                            v___y_2373_,
                            v___y_2374_,
                            v___y_2375_,
                            v_a_2425_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_2430_) == 0 {
                            v_a_2431_ = crate::leanh::lean_ctor_get(v___x_2430_, 0);
                            crate::leanh::lean_inc(v_a_2431_);
                            v_a_2432_ = crate::leanh::lean_ctor_get(v___x_2430_, 1);
                            crate::leanh::lean_inc(v_a_2432_);
                            crate::leanh::lean_dec_ref_known(v___x_2430_, 2);
                            v___x_2433_ = l_Lake_Job_await___redArg(v_a_2431_, v_a_2432_);
                            if crate::leanh::lean_obj_tag(v___x_2433_) == 0 {
                                v_a_2434_ = crate::leanh::lean_ctor_get(v___x_2433_, 0);
                                crate::leanh::lean_inc(v_a_2434_);
                                v_a_2435_ = crate::leanh::lean_ctor_get(v___x_2433_, 1);
                                crate::leanh::lean_inc(v_a_2435_);
                                crate::leanh::lean_dec_ref_known(v___x_2433_, 2);
                                v___x_2436_ = lean_array_push(v_a_2434_, v_pkg_2363_);
                                v_sz_2437_ = lean_array_size(v___x_2436_);
                                crate::leanh::lean_inc_ref(v___y_2371_);
                                v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(v___x_2436_, v_sz_2437_, v___x_2360_, v_fst_2420_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2435_);
                                crate::leanh::lean_dec_ref(v___x_2436_);
                                if crate::leanh::lean_obj_tag(v___x_2438_) == 0 {
                                    v_toLeanConfig_2439_ =
                                        crate::leanh::lean_ctor_get(v_config_2383_, 1);
                                    crate::leanh::lean_inc_ref(v_toLeanConfig_2439_);
                                    v_a_2440_ = crate::leanh::lean_ctor_get(v___x_2438_, 0);
                                    v_a_2441_ = crate::leanh::lean_ctor_get(v___x_2438_, 1);
                                    v_isSharedCheck_2464_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2438_)) as u8;
                                    if v_isSharedCheck_2464_ == 0 {
                                        v___x_2443_ = v___x_2438_;
                                        v_isShared_2444_ = v_isSharedCheck_2464_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2441_);
                                        crate::leanh::lean_inc(v_a_2440_);
                                        crate::leanh::lean_dec(v___x_2438_);
                                        v___x_2443_ = crate::leanh::lean_box(0);
                                        v_isShared_2444_ = v_isSharedCheck_2464_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2424_);
                                    crate::leanh::lean_dec_ref(v_config_2383_);
                                    crate::leanh::lean_dec_ref(v_dir_2382_);
                                    crate::leanh::lean_dec_ref(v___y_2371_);
                                    crate::leanh::lean_dec_ref(v_self_2369_);
                                    crate::leanh::lean_dec_ref(v_exeName_2368_);
                                    crate::leanh::lean_dec(v___x_2362_);
                                    v_a_2465_ = crate::leanh::lean_ctor_get(v___x_2438_, 0);
                                    v_a_2466_ = crate::leanh::lean_ctor_get(v___x_2438_, 1);
                                    v_isSharedCheck_2473_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2438_)) as u8;
                                    if v_isSharedCheck_2473_ == 0 {
                                        v___x_2468_ = v___x_2438_;
                                        v_isShared_2469_ = v_isSharedCheck_2473_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2466_);
                                        crate::leanh::lean_inc(v_a_2465_);
                                        crate::leanh::lean_dec(v___x_2438_);
                                        v___x_2468_ = crate::leanh::lean_box(0);
                                        v_isShared_2469_ = v_isSharedCheck_2473_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2424_);
                                crate::leanh::lean_dec(v_fst_2420_);
                                crate::leanh::lean_dec_ref(v_config_2383_);
                                crate::leanh::lean_dec_ref(v_dir_2382_);
                                crate::leanh::lean_dec_ref(v___y_2371_);
                                crate::leanh::lean_dec_ref(v_self_2369_);
                                crate::leanh::lean_dec_ref(v_exeName_2368_);
                                crate::leanh::lean_dec_ref(v_pkg_2363_);
                                crate::leanh::lean_dec(v___x_2362_);
                                v_a_2474_ = crate::leanh::lean_ctor_get(v___x_2433_, 0);
                                v_a_2475_ = crate::leanh::lean_ctor_get(v___x_2433_, 1);
                                v_isSharedCheck_2482_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2433_)) as u8;
                                if v_isSharedCheck_2482_ == 0 {
                                    v___x_2477_ = v___x_2433_;
                                    v_isShared_2478_ = v_isSharedCheck_2482_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2475_);
                                    crate::leanh::lean_inc(v_a_2474_);
                                    crate::leanh::lean_dec(v___x_2433_);
                                    v___x_2477_ = crate::leanh::lean_box(0);
                                    v_isShared_2478_ = v_isSharedCheck_2482_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2424_);
                            crate::leanh::lean_dec(v_fst_2420_);
                            crate::leanh::lean_dec_ref(v_config_2383_);
                            crate::leanh::lean_dec_ref(v_dir_2382_);
                            crate::leanh::lean_dec_ref(v___y_2371_);
                            crate::leanh::lean_dec_ref(v_self_2369_);
                            crate::leanh::lean_dec_ref(v_exeName_2368_);
                            crate::leanh::lean_dec_ref(v_pkg_2363_);
                            crate::leanh::lean_dec(v___x_2362_);
                            v_a_2483_ = crate::leanh::lean_ctor_get(v___x_2430_, 0);
                            v_a_2484_ = crate::leanh::lean_ctor_get(v___x_2430_, 1);
                            v_isSharedCheck_2491_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2430_)) as u8;
                            if v_isSharedCheck_2491_ == 0 {
                                v___x_2486_ = v___x_2430_;
                                v_isShared_2487_ = v_isSharedCheck_2491_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2484_);
                                crate::leanh::lean_inc(v_a_2483_);
                                crate::leanh::lean_dec(v___x_2430_);
                                v___x_2486_ = crate::leanh::lean_box(0);
                                v_isShared_2487_ = v_isSharedCheck_2491_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_2420_);
                        crate::leanh::lean_dec_ref(v_config_2383_);
                        crate::leanh::lean_dec_ref(v_dir_2382_);
                        crate::leanh::lean_dec_ref(v___y_2371_);
                        crate::leanh::lean_dec_ref(v_self_2369_);
                        crate::leanh::lean_dec_ref(v_exeName_2368_);
                        crate::leanh::lean_dec_ref(v_pkg_2363_);
                        crate::leanh::lean_dec(v___x_2362_);
                        v_a_2492_ = crate::leanh::lean_ctor_get(v___x_2423_, 0);
                        v_a_2493_ = crate::leanh::lean_ctor_get(v___x_2423_, 1);
                        v_isSharedCheck_2500_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2423_)) as u8;
                        if v_isSharedCheck_2500_ == 0 {
                            v___x_2495_ = v___x_2423_;
                            v_isShared_2496_ = v_isSharedCheck_2500_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2493_);
                            crate::leanh::lean_inc(v_a_2492_);
                            crate::leanh::lean_dec(v___x_2423_);
                            v___x_2495_ = crate::leanh::lean_box(0);
                            v_isShared_2496_ = v_isSharedCheck_2500_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_2383_);
                    crate::leanh::lean_dec_ref(v_dir_2382_);
                    crate::leanh::lean_dec_ref(v___y_2371_);
                    crate::leanh::lean_dec_ref(v_self_2369_);
                    crate::leanh::lean_dec_ref(v_exeName_2368_);
                    crate::leanh::lean_dec_ref(v_pkg_2363_);
                    crate::leanh::lean_dec(v___x_2362_);
                    v_a_2501_ = crate::leanh::lean_ctor_get(v___x_2417_, 0);
                    v_a_2502_ = crate::leanh::lean_ctor_get(v___x_2417_, 1);
                    v_isSharedCheck_2509_ = (!crate::leanh::lean_is_exclusive(v___x_2417_)) as u8;
                    if v_isSharedCheck_2509_ == 0 {
                        v___x_2504_ = v___x_2417_;
                        v_isShared_2505_ = v_isSharedCheck_2509_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2502_);
                        crate::leanh::lean_inc(v_a_2501_);
                        crate::leanh::lean_dec(v___x_2417_);
                        v___x_2504_ = crate::leanh::lean_box(0);
                        v_isShared_2505_ = v_isSharedCheck_2509_;
                        state = 15;
                        continue;
                    }
                }
            }
            5 => {
                v_buildDir_2445_ = crate::leanh::lean_ctor_get(v_config_2383_, 5);
                crate::leanh::lean_inc_ref(v_buildDir_2445_);
                v_binDir_2446_ = crate::leanh::lean_ctor_get(v_config_2383_, 8);
                crate::leanh::lean_inc_ref(v_binDir_2446_);
                crate::leanh::lean_dec_ref(v_config_2383_);
                v_weakLinkArgs_2447_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2439_, 9);
                crate::leanh::lean_inc_ref(v_weakLinkArgs_2447_);
                crate::leanh::lean_dec_ref(v_toLeanConfig_2439_);
                v___x_2448_ = l_System_FilePath_normalize(v_buildDir_2445_);
                v___x_2449_ = l_Lake_joinRelative(v_dir_2382_, v___x_2448_);
                v___x_2450_ = l_System_FilePath_normalize(v_binDir_2446_);
                v___x_2451_ = l_Lake_joinRelative(v___x_2449_, v___x_2450_);
                v___x_2452_ = l_System_FilePath_exeExtension;
                v___x_2453_ = l_System_FilePath_addExtension(v_exeName_2368_, v___x_2452_);
                v___x_2454_ = l_Lake_joinRelative(v___x_2451_, v___x_2453_);
                v___x_2455_ = l_Array_append___redArg(v_weakLinkArgs_2447_, v_weakLinkArgs_2403_);
                v___x_2456_ = l_Lake_LeanExe_linkArgs(v_self_2369_);
                v___x_2457_ = l_System_Platform_isWindows;
                v___x_2458_ = lean_strict_and(v___x_2457_, v_supportInterpreter_2365_);
                v___x_2459_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1_once), _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1);
                v___x_2460_ = l_Lake_buildLeanExe(
                    v___x_2454_,
                    v_a_2440_,
                    v_a_2424_,
                    v___x_2455_,
                    v___x_2456_,
                    v___x_2458_,
                    v___y_2371_,
                    v___x_2362_,
                    v___y_2373_,
                    v___y_2374_,
                    v___y_2375_,
                    v___x_2459_,
                );
                crate::leanh::lean_dec(v___x_2362_);
                crate::leanh::lean_dec(v_a_2440_);
                if v_isShared_2444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2460_);
                    v___x_2462_ = v___x_2443_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_a_2441_);
                    v___x_2462_ = v_reuseFailAlloc_2463_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2462_;
            }
            7 => {
                if v_isShared_2469_ == 0 {
                    v___x_2471_ = v___x_2468_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2472_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_a_2466_);
                    v___x_2471_ = v_reuseFailAlloc_2472_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2471_;
            }
            9 => {
                if v_isShared_2478_ == 0 {
                    v___x_2480_ = v___x_2477_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2481_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_a_2475_);
                    v___x_2480_ = v_reuseFailAlloc_2481_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2480_;
            }
            11 => {
                if v_isShared_2487_ == 0 {
                    v___x_2489_ = v___x_2486_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_a_2484_);
                    v___x_2489_ = v_reuseFailAlloc_2490_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2489_;
            }
            13 => {
                if v_isShared_2496_ == 0 {
                    v___x_2498_ = v___x_2495_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_a_2493_);
                    v___x_2498_ = v_reuseFailAlloc_2499_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2498_;
            }
            15 => {
                if v_isShared_2505_ == 0 {
                    v___x_2507_ = v___x_2504_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2508_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_a_2502_);
                    v___x_2507_ = v_reuseFailAlloc_2508_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2507_;
            }
            17 => {
                if v_isShared_2525_ == 0 {
                    v___x_2527_ = v___x_2524_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_a_2522_);
                    v___x_2527_ = v_reuseFailAlloc_2528_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2527_;
            }
            19 => {
                if v_isShared_2534_ == 0 {
                    v___x_2536_ = v___x_2533_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2537_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_a_2531_);
                    v___x_2536_ = v_reuseFailAlloc_2537_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2536_;
            }
            21 => {
                return v___x_2550_;
            }
            22 => {
                if v_isShared_2557_ == 0 {
                    v___x_2559_ = v___x_2556_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2560_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_a_2554_);
                    v___x_2559_ = v_reuseFailAlloc_2560_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2559_;
            }
            24 => {
                if v_isShared_2566_ == 0 {
                    v___x_2568_ = v___x_2565_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_a_2563_);
                    v___x_2568_ = v_reuseFailAlloc_2569_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2571_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2572_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_2573_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2574_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_objJobs_2575_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2576_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_pkg_2577_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_root_2578_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_supportInterpreter_2579_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_toLeanConfig_2580_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_libJobs_2581_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_exeName_2582_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_self_2583_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_2584_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2585_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2586_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2587_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2588_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2589_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2590_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2591_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_sz_boxed_2592_: usize = 0;
    let mut v___x_108882__boxed_2593_: usize = 0;
    let mut v_supportInterpreter_boxed_2594_: u8 = 0;
    let mut v_res_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2592_ = crate::leanh::lean_unbox_usize(v_sz_2573_);
    crate::leanh::lean_dec(v_sz_2573_);
    v___x_108882__boxed_2593_ = crate::leanh::lean_unbox_usize(v___x_2574_);
    crate::leanh::lean_dec(v___x_2574_);
    v_supportInterpreter_boxed_2594_ = (crate::leanh::lean_unbox(v_supportInterpreter_2579_) as u8);
    v_res_2595_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(
        v___x_2571_,
        v___x_2572_,
        v_sz_boxed_2592_,
        v___x_108882__boxed_2593_,
        v_objJobs_2575_,
        v___x_2576_,
        v_pkg_2577_,
        v_root_2578_,
        v_supportInterpreter_boxed_2594_,
        v_toLeanConfig_2580_,
        v_libJobs_2581_,
        v_exeName_2582_,
        v_self_2583_,
        v___x_2584_,
        v___y_2585_,
        v___y_2586_,
        v___y_2587_,
        v___y_2588_,
        v___y_2589_,
        v___y_2590_,
    );
    crate::leanh::lean_dec_ref(v___y_2589_);
    crate::leanh::lean_dec(v___y_2588_);
    crate::leanh::lean_dec(v___y_2587_);
    crate::leanh::lean_dec(v___y_2586_);
    crate::leanh::lean_dec(v___x_2584_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2580_);
    crate::leanh::lean_dec_ref(v___x_2572_);
    return v_res_2595_;
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(
    mut v_self_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
    mut v_a_2603_: *mut crate::leanh::LeanObject,
    mut v_a_2604_: *mut crate::leanh::LeanObject,
    mut v_a_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_2615_: u8 = 0;
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objJobs_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2625_: usize = 0;
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2636_: u8 = 0;
    let mut v_task_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v_registeredJobs_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u8 = 0;
    let mut v_job_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_unused_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_2609_ = crate::leanh::lean_ctor_get(v_self_2601_, 2);
                v_pkg_2610_ = crate::leanh::lean_ctor_get(v_self_2601_, 0);
                crate::leanh::lean_inc_ref_n(v_pkg_2610_, 3);
                v_name_2611_ = crate::leanh::lean_ctor_get(v_self_2601_, 1);
                crate::leanh::lean_inc_n(v_name_2611_, 2);
                v_toLeanConfig_2612_ = crate::leanh::lean_ctor_get(v_config_2609_, 0);
                crate::leanh::lean_inc_ref(v_toLeanConfig_2612_);
                v_root_2613_ = crate::leanh::lean_ctor_get(v_config_2609_, 2);
                crate::leanh::lean_inc_n(v_root_2613_, 2);
                v_exeName_2614_ = crate::leanh::lean_ctor_get(v_config_2609_, 3);
                crate::leanh::lean_inc_ref(v_exeName_2614_);
                v_supportInterpreter_2615_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_2609_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v___x_2616_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_2609_);
                v_nativeFacets_2617_ = crate::leanh::lean_ctor_get(v___x_2616_, 8);
                crate::leanh::lean_inc_ref(v_nativeFacets_2617_);
                v___x_2618_ = l_Lake_instDataKindFilePath;
                v___x_2619_ = crate::leanh::lean_unsigned_to_nat(0);
                v_objJobs_2620_ =
                    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0;
                v___x_2621_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2621_, 0, v_pkg_2610_);
                crate::leanh::lean_ctor_set(v___x_2621_, 1, v_name_2611_);
                crate::leanh::lean_ctor_set(v___x_2621_, 2, v___x_2616_);
                v___x_2622_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2622_, 0, v___x_2621_);
                crate::leanh::lean_ctor_set(v___x_2622_, 1, v_root_2613_);
                v___x_2623_ = crate::leanh::lean_box((v_supportInterpreter_2615_) as usize);
                v___x_2624_ = crate::leanh::lean_apply_1(v_nativeFacets_2617_, v___x_2623_);
                v_sz_2625_ = lean_array_size(v___x_2624_);
                v___x_2626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2626_, 0, v_pkg_2610_);
                v___x_2627_ = crate::leanh::lean_box_usize(v_sz_2625_);
                v___x_2628_ =
                    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1;
                v___x_2629_ = crate::leanh::lean_box((v_supportInterpreter_2615_) as usize);
                v___f_2630_ = crate::leanh::lean_alloc_closure(
                    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed
                        as *mut core::ffi::c_void,
                    21,
                    14,
                );
                crate::leanh::lean_closure_set(v___f_2630_, 0, v___x_2622_);
                crate::leanh::lean_closure_set(v___f_2630_, 1, v___x_2624_);
                crate::leanh::lean_closure_set(v___f_2630_, 2, v___x_2627_);
                crate::leanh::lean_closure_set(v___f_2630_, 3, v___x_2628_);
                crate::leanh::lean_closure_set(v___f_2630_, 4, v_objJobs_2620_);
                crate::leanh::lean_closure_set(v___f_2630_, 5, v___x_2626_);
                crate::leanh::lean_closure_set(v___f_2630_, 6, v_pkg_2610_);
                crate::leanh::lean_closure_set(v___f_2630_, 7, v_root_2613_);
                crate::leanh::lean_closure_set(v___f_2630_, 8, v___x_2629_);
                crate::leanh::lean_closure_set(v___f_2630_, 9, v_toLeanConfig_2612_);
                crate::leanh::lean_closure_set(v___f_2630_, 10, v_objJobs_2620_);
                crate::leanh::lean_closure_set(v___f_2630_, 11, v_exeName_2614_);
                crate::leanh::lean_closure_set(v___f_2630_, 12, v_self_2601_);
                crate::leanh::lean_closure_set(v___f_2630_, 13, v___x_2619_);
                v___x_2631_ = l_Lake_ensureJob___redArg(
                    v___x_2618_,
                    v___f_2630_,
                    v_a_2602_,
                    v_a_2603_,
                    v_a_2604_,
                    v_a_2605_,
                    v_a_2606_,
                    v_a_2607_,
                );
                if crate::leanh::lean_obj_tag(v___x_2631_) == 0 {
                    v_a_2632_ = crate::leanh::lean_ctor_get(v___x_2631_, 0);
                    v_a_2633_ = crate::leanh::lean_ctor_get(v___x_2631_, 1);
                    v_isSharedCheck_2661_ = (!crate::leanh::lean_is_exclusive(v___x_2631_)) as u8;
                    if v_isSharedCheck_2661_ == 0 {
                        v___x_2635_ = v___x_2631_;
                        v_isShared_2636_ = v_isSharedCheck_2661_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2633_);
                        crate::leanh::lean_inc(v_a_2632_);
                        crate::leanh::lean_dec(v___x_2631_);
                        v___x_2635_ = crate::leanh::lean_box(0);
                        v_isShared_2636_ = v_isSharedCheck_2661_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_2611_);
                    return v___x_2631_;
                }
            }
            1 => {
                v_task_2637_ = crate::leanh::lean_ctor_get(v_a_2632_, 0);
                v_kind_2638_ = crate::leanh::lean_ctor_get(v_a_2632_, 1);
                v_isSharedCheck_2659_ = (!crate::leanh::lean_is_exclusive(v_a_2632_)) as u8;
                if v_isSharedCheck_2659_ == 0 {
                    v_unused_2660_ = crate::leanh::lean_ctor_get(v_a_2632_, 2);
                    crate::leanh::lean_dec(v_unused_2660_);
                    v___x_2640_ = v_a_2632_;
                    v_isShared_2641_ = v_isSharedCheck_2659_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_2638_);
                    crate::leanh::lean_inc(v_task_2637_);
                    crate::leanh::lean_dec(v_a_2632_);
                    v___x_2640_ = crate::leanh::lean_box(0);
                    v_isShared_2641_ = v_isSharedCheck_2659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_2642_ = crate::leanh::lean_ctor_get(v_a_2606_, 3);
                v___x_2643_ = lean_st_ref_take(v_registeredJobs_2642_);
                v___x_2644_ = 1;
                v___x_2645_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_2611_,
                    v___x_2644_,
                );
                v___x_2646_ =
                    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1;
                v___x_2647_ = lean_string_append(v___x_2645_, v___x_2646_);
                v___x_2648_ = 0;
                if v_isShared_2641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2640_, 2, v___x_2647_);
                    v_job_2650_ = v___x_2640_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_task_2637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_kind_2638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 2, v___x_2647_);
                    v_job_2650_ = v_reuseFailAlloc_2658_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_2650_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2648_,
                );
                crate::leanh::lean_inc_ref(v_job_2650_);
                v___x_2651_ = l_Lake_Job_toOpaque___redArg(v_job_2650_);
                v___x_2652_ = lean_array_push(v___x_2643_, v___x_2651_);
                v___x_2653_ = lean_st_ref_set(v_registeredJobs_2642_, v___x_2652_);
                v___x_2654_ = l_Lake_Job_renew___redArg(v_job_2650_);
                if v_isShared_2636_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2635_, 0, v___x_2654_);
                    v___x_2656_ = v___x_2635_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_a_2633_);
                    v___x_2656_ = v_reuseFailAlloc_2657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(
    mut v_self_2662_: *mut crate::leanh::LeanObject,
    mut v_a_2663_: *mut crate::leanh::LeanObject,
    mut v_a_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
    mut v_a_2669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2670_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(
        v_self_2662_,
        v_a_2663_,
        v_a_2664_,
        v_a_2665_,
        v_a_2666_,
        v_a_2667_,
        v_a_2668_,
    );
    crate::leanh::lean_dec_ref(v_a_2667_);
    crate::leanh::lean_dec(v_a_2666_);
    crate::leanh::lean_dec(v_a_2665_);
    crate::leanh::lean_dec(v_a_2664_);
    return v_res_2670_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(
    mut v_00_u03b2_2671_: *mut crate::leanh::LeanObject,
    mut v_m_2672_: *mut crate::leanh::LeanObject,
    mut v_a_2673_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2674_: u8 = 0;
    v___x_2674_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(v_m_2672_, v_a_2673_);
    return v___x_2674_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___boxed(
    mut v_00_u03b2_2675_: *mut crate::leanh::LeanObject,
    mut v_m_2676_: *mut crate::leanh::LeanObject,
    mut v_a_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2678_: u8 = 0;
    let mut v_r_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(v_00_u03b2_2675_, v_m_2676_, v_a_2677_);
    crate::leanh::lean_dec_ref(v_a_2677_);
    crate::leanh::lean_dec_ref(v_m_2676_);
    v_r_2679_ = crate::leanh::lean_box((v_res_2678_) as usize);
    return v_r_2679_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1(
    mut v_00_u03b2_2680_: *mut crate::leanh::LeanObject,
    mut v_m_2681_: *mut crate::leanh::LeanObject,
    mut v_a_2682_: *mut crate::leanh::LeanObject,
    mut v_b_2683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2684_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(v_m_2681_, v_a_2682_, v_b_2683_);
    return v___x_2684_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4(
    mut v_00_u03b2_2685_: *mut crate::leanh::LeanObject,
    mut v_a_2686_: *mut crate::leanh::LeanObject,
    mut v_x_2687_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2688_: u8 = 0;
    v___x_2688_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(v_a_2686_, v_x_2687_);
    return v___x_2688_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b2_2689_: *mut crate::leanh::LeanObject,
    mut v_a_2690_: *mut crate::leanh::LeanObject,
    mut v_x_2691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2692_: u8 = 0;
    let mut v_r_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2692_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4(v_00_u03b2_2689_, v_a_2690_, v_x_2691_);
    crate::leanh::lean_dec(v_x_2691_);
    crate::leanh::lean_dec_ref(v_a_2690_);
    v_r_2693_ = crate::leanh::lean_box((v_res_2692_) as usize);
    return v_r_2693_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6(
    mut v_00_u03b2_2694_: *mut crate::leanh::LeanObject,
    mut v_data_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(v_data_2695_);
    return v___x_2696_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18(
    mut v_00_u03b2_2697_: *mut crate::leanh::LeanObject,
    mut v_i_2698_: *mut crate::leanh::LeanObject,
    mut v_source_2699_: *mut crate::leanh::LeanObject,
    mut v_target_2700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2701_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(v_i_2698_, v_source_2699_, v_target_2700_);
    return v___x_2701_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19(
    mut v_00_u03b2_2702_: *mut crate::leanh::LeanObject,
    mut v_x_2703_: *mut crate::leanh::LeanObject,
    mut v_x_2704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(v_x_2703_, v_x_2704_);
    return v___x_2705_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(
    mut v_fmt_2706_: u8,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_fmt_2706_ == 0 {
        return v_a_2707_;
    } else {
        let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2708_ = l_Lake_mkRelPathString(v_a_2707_);
        v___x_2709_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2709_, 0, v___x_2708_);
        v___x_2710_ = l_Lean_Json_compress(v___x_2709_);
        return v___x_2710_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(
    mut v_fmt_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fmt_boxed_2713_: u8 = 0;
    let mut v_res_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fmt_boxed_2713_ = (crate::leanh::lean_unbox(v_fmt_2711_) as u8);
    v_res_2714_ = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(
        v_fmt_boxed_2713_,
        v_a_2712_,
    );
    return v_res_2714_;
}
pub unsafe fn _init_l_Lake_LeanExe_exeFacetConfig___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___f_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: u8 = 0;
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2717_ = l_Lake_LeanExe_exeFacetConfig___closed__0;
    v___x_2718_ = 1;
    v___x_2719_ = l_Lake_instDataKindFilePath;
    v___x_2720_ = l_Lake_LeanExe_exeFacetConfig___closed__1;
    v___x_2721_ = l_Lake_LeanExe_keyword;
    v___x_2722_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2722_, 0, v___x_2721_);
    crate::leanh::lean_ctor_set(v___x_2722_, 1, v___x_2720_);
    crate::leanh::lean_ctor_set(v___x_2722_, 2, v___x_2719_);
    crate::leanh::lean_ctor_set(v___x_2722_, 3, v___f_2717_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2722_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_2718_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2722_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v___x_2718_,
    );
    return v___x_2722_;
}
pub unsafe fn _init_l_Lake_LeanExe_exeFacetConfig() -> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExe_exeFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LeanExe_exeFacetConfig___closed__2_once),
        _init_l_Lake_LeanExe_exeFacetConfig___closed__2,
    );
    return v___x_2723_;
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(
    mut v_lib_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_2732_ = crate::leanh::lean_ctor_get(v_lib_2724_, 0);
    v_name_2733_ = crate::leanh::lean_ctor_get(v_lib_2724_, 1);
    v_keyName_2734_ = crate::leanh::lean_ctor_get(v_pkg_2732_, 2);
    v___x_2735_ = l_Lake_LeanExe_exeFacet;
    crate::leanh::lean_inc(v_name_2733_);
    crate::leanh::lean_inc(v_keyName_2734_);
    v___x_2736_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2736_, 0, v_keyName_2734_);
    crate::leanh::lean_ctor_set(v___x_2736_, 1, v_name_2733_);
    v___x_2737_ = l_Lake_LeanExe_keyword;
    v___x_2738_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2738_, 0, v___x_2736_);
    crate::leanh::lean_ctor_set(v___x_2738_, 1, v___x_2737_);
    crate::leanh::lean_ctor_set(v___x_2738_, 2, v_lib_2724_);
    crate::leanh::lean_ctor_set(v___x_2738_, 3, v___x_2735_);
    crate::leanh::lean_inc_ref(v_a_2729_);
    crate::leanh::lean_inc(v_a_2728_);
    crate::leanh::lean_inc(v_a_2727_);
    crate::leanh::lean_inc(v_a_2726_);
    v___x_2739_ = crate::leanh::lean_apply_7(
        v_a_2725_,
        v___x_2738_,
        v_a_2726_,
        v_a_2727_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        crate::leanh::lean_box(0),
    );
    return v___x_2739_;
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(
    mut v_lib_2740_: *mut crate::leanh::LeanObject,
    mut v_a_2741_: *mut crate::leanh::LeanObject,
    mut v_a_2742_: *mut crate::leanh::LeanObject,
    mut v_a_2743_: *mut crate::leanh::LeanObject,
    mut v_a_2744_: *mut crate::leanh::LeanObject,
    mut v_a_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2748_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(
        v_lib_2740_,
        v_a_2741_,
        v_a_2742_,
        v_a_2743_,
        v_a_2744_,
        v_a_2745_,
        v_a_2746_,
    );
    crate::leanh::lean_dec_ref(v_a_2745_);
    crate::leanh::lean_dec(v_a_2744_);
    crate::leanh::lean_dec(v_a_2743_);
    crate::leanh::lean_dec(v_a_2742_);
    return v_res_2748_;
}
pub unsafe fn _init_l_Lake_LeanExe_defaultFacetConfig___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2750_: u8 = 0;
    let mut v___f_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2750_ = 0;
    v___f_2751_ = l_Lake_LeanExe_exeFacetConfig___closed__0;
    v___x_2752_ = 1;
    v___x_2753_ = l_Lake_instDataKindFilePath;
    v___x_2754_ = l_Lake_LeanExe_defaultFacetConfig___closed__0;
    v___x_2755_ = l_Lake_LeanExe_keyword;
    v___x_2756_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2756_, 0, v___x_2755_);
    crate::leanh::lean_ctor_set(v___x_2756_, 1, v___x_2754_);
    crate::leanh::lean_ctor_set(v___x_2756_, 2, v___x_2753_);
    crate::leanh::lean_ctor_set(v___x_2756_, 3, v___f_2751_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2756_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_2752_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2756_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v___x_2750_,
    );
    return v___x_2756_;
}
pub unsafe fn _init_l_Lake_LeanExe_defaultFacetConfig() -> *mut crate::leanh::LeanObject {
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2757_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExe_defaultFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanExe_defaultFacetConfig___closed__1_once),
        _init_l_Lake_LeanExe_defaultFacetConfig___closed__1,
    );
    return v___x_2757_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(
    mut v_k_2758_: *mut crate::leanh::LeanObject,
    mut v_v_2759_: *mut crate::leanh::LeanObject,
    mut v_t_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2768_: u8 = 0;
    let mut v___x_2769_: u8 = 0;
    let mut v_impl_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v_size_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut v_unused_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_unused_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_unused_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v_unused_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2879_: u8 = 0;
    let mut v_k_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v_unused_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut v_unused_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v_size_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v_unused_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2982_: u8 = 0;
    let mut v_unused_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_unused_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v_k_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut v_unused_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut v_unused_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2760_) == 0 {
                    v_size_2761_ = crate::leanh::lean_ctor_get(v_t_2760_, 0);
                    v_k_2762_ = crate::leanh::lean_ctor_get(v_t_2760_, 1);
                    v_v_2763_ = crate::leanh::lean_ctor_get(v_t_2760_, 2);
                    v_l_2764_ = crate::leanh::lean_ctor_get(v_t_2760_, 3);
                    v_r_2765_ = crate::leanh::lean_ctor_get(v_t_2760_, 4);
                    v_isSharedCheck_3045_ = (!crate::leanh::lean_is_exclusive(v_t_2760_)) as u8;
                    if v_isSharedCheck_3045_ == 0 {
                        v___x_2767_ = v_t_2760_;
                        v_isShared_2768_ = v_isSharedCheck_3045_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_2765_);
                        crate::leanh::lean_inc(v_l_2764_);
                        crate::leanh::lean_inc(v_v_2763_);
                        crate::leanh::lean_inc(v_k_2762_);
                        crate::leanh::lean_inc(v_size_2761_);
                        crate::leanh::lean_dec(v_t_2760_);
                        v___x_2767_ = crate::leanh::lean_box(0);
                        v_isShared_2768_ = v_isSharedCheck_3045_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3046_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3047_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3047_, 0, v___x_3046_);
                    crate::leanh::lean_ctor_set(v___x_3047_, 1, v_k_2758_);
                    crate::leanh::lean_ctor_set(v___x_3047_, 2, v_v_2759_);
                    crate::leanh::lean_ctor_set(v___x_3047_, 3, v_t_2760_);
                    crate::leanh::lean_ctor_set(v___x_3047_, 4, v_t_2760_);
                    return v___x_3047_;
                }
            }
            1 => {
                v___x_2769_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2758_, v_k_2762_);
                match v___x_2769_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_2761_);
                        v_impl_2770_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_2758_, v_v_2759_, v_l_2764_);
                        v___x_2771_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_2765_) == 0 {
                            v_size_2772_ = crate::leanh::lean_ctor_get(v_r_2765_, 0);
                            v_size_2773_ = crate::leanh::lean_ctor_get(v_impl_2770_, 0);
                            crate::leanh::lean_inc(v_size_2773_);
                            v_k_2774_ = crate::leanh::lean_ctor_get(v_impl_2770_, 1);
                            crate::leanh::lean_inc(v_k_2774_);
                            v_v_2775_ = crate::leanh::lean_ctor_get(v_impl_2770_, 2);
                            crate::leanh::lean_inc(v_v_2775_);
                            v_l_2776_ = crate::leanh::lean_ctor_get(v_impl_2770_, 3);
                            crate::leanh::lean_inc(v_l_2776_);
                            v_r_2777_ = crate::leanh::lean_ctor_get(v_impl_2770_, 4);
                            crate::leanh::lean_inc(v_r_2777_);
                            v___x_2778_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2779_ = lean_nat_mul(v___x_2778_, v_size_2772_);
                            v___x_2780_ = lean_nat_dec_lt(v___x_2779_, v_size_2773_);
                            crate::leanh::lean_dec(v___x_2779_);
                            if v___x_2780_ == 0 {
                                crate::leanh::lean_dec(v_r_2777_);
                                crate::leanh::lean_dec(v_l_2776_);
                                crate::leanh::lean_dec(v_v_2775_);
                                crate::leanh::lean_dec(v_k_2774_);
                                v___x_2781_ = lean_nat_add(v___x_2771_, v_size_2773_);
                                crate::leanh::lean_dec(v_size_2773_);
                                v___x_2782_ = lean_nat_add(v___x_2781_, v_size_2772_);
                                crate::leanh::lean_dec(v___x_2781_);
                                if v_isShared_2768_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2767_, 3, v_impl_2770_);
                                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2782_);
                                    v___x_2784_ = v___x_2767_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2785_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        0,
                                        v___x_2782_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        1,
                                        v_k_2762_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        2,
                                        v_v_2763_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        3,
                                        v_impl_2770_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        4,
                                        v_r_2765_,
                                    );
                                    v___x_2784_ = v_reuseFailAlloc_2785_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2851_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2770_)) as u8;
                                if v_isSharedCheck_2851_ == 0 {
                                    v_unused_2852_ = crate::leanh::lean_ctor_get(v_impl_2770_, 4);
                                    crate::leanh::lean_dec(v_unused_2852_);
                                    v_unused_2853_ = crate::leanh::lean_ctor_get(v_impl_2770_, 3);
                                    crate::leanh::lean_dec(v_unused_2853_);
                                    v_unused_2854_ = crate::leanh::lean_ctor_get(v_impl_2770_, 2);
                                    crate::leanh::lean_dec(v_unused_2854_);
                                    v_unused_2855_ = crate::leanh::lean_ctor_get(v_impl_2770_, 1);
                                    crate::leanh::lean_dec(v_unused_2855_);
                                    v_unused_2856_ = crate::leanh::lean_ctor_get(v_impl_2770_, 0);
                                    crate::leanh::lean_dec(v_unused_2856_);
                                    v___x_2787_ = v_impl_2770_;
                                    v_isShared_2788_ = v_isSharedCheck_2851_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2770_);
                                    v___x_2787_ = crate::leanh::lean_box(0);
                                    v_isShared_2788_ = v_isSharedCheck_2851_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2857_ = crate::leanh::lean_ctor_get(v_impl_2770_, 3);
                            crate::leanh::lean_inc(v_l_2857_);
                            if crate::leanh::lean_obj_tag(v_l_2857_) == 0 {
                                v_r_2858_ = crate::leanh::lean_ctor_get(v_impl_2770_, 4);
                                v_k_2859_ = crate::leanh::lean_ctor_get(v_impl_2770_, 1);
                                v_v_2860_ = crate::leanh::lean_ctor_get(v_impl_2770_, 2);
                                v_isSharedCheck_2871_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2770_)) as u8;
                                if v_isSharedCheck_2871_ == 0 {
                                    v_unused_2872_ = crate::leanh::lean_ctor_get(v_impl_2770_, 3);
                                    crate::leanh::lean_dec(v_unused_2872_);
                                    v_unused_2873_ = crate::leanh::lean_ctor_get(v_impl_2770_, 0);
                                    crate::leanh::lean_dec(v_unused_2873_);
                                    v___x_2862_ = v_impl_2770_;
                                    v_isShared_2863_ = v_isSharedCheck_2871_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2858_);
                                    crate::leanh::lean_inc(v_v_2860_);
                                    crate::leanh::lean_inc(v_k_2859_);
                                    crate::leanh::lean_dec(v_impl_2770_);
                                    v___x_2862_ = crate::leanh::lean_box(0);
                                    v_isShared_2863_ = v_isSharedCheck_2871_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2874_ = crate::leanh::lean_ctor_get(v_impl_2770_, 4);
                                crate::leanh::lean_inc(v_r_2874_);
                                if crate::leanh::lean_obj_tag(v_r_2874_) == 0 {
                                    v_k_2875_ = crate::leanh::lean_ctor_get(v_impl_2770_, 1);
                                    v_v_2876_ = crate::leanh::lean_ctor_get(v_impl_2770_, 2);
                                    v_isSharedCheck_2899_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2770_)) as u8;
                                    if v_isSharedCheck_2899_ == 0 {
                                        v_unused_2900_ =
                                            crate::leanh::lean_ctor_get(v_impl_2770_, 4);
                                        crate::leanh::lean_dec(v_unused_2900_);
                                        v_unused_2901_ =
                                            crate::leanh::lean_ctor_get(v_impl_2770_, 3);
                                        crate::leanh::lean_dec(v_unused_2901_);
                                        v_unused_2902_ =
                                            crate::leanh::lean_ctor_get(v_impl_2770_, 0);
                                        crate::leanh::lean_dec(v_unused_2902_);
                                        v___x_2878_ = v_impl_2770_;
                                        v_isShared_2879_ = v_isSharedCheck_2899_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2876_);
                                        crate::leanh::lean_inc(v_k_2875_);
                                        crate::leanh::lean_dec(v_impl_2770_);
                                        v___x_2878_ = crate::leanh::lean_box(0);
                                        v_isShared_2879_ = v_isSharedCheck_2899_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_2903_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2768_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2767_, 4, v_r_2874_);
                                        crate::leanh::lean_ctor_set(v___x_2767_, 3, v_impl_2770_);
                                        crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2903_);
                                        v___x_2905_ = v___x_2767_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2906_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            0,
                                            v___x_2903_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            1,
                                            v_k_2762_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            2,
                                            v_v_2763_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            3,
                                            v_impl_2770_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            4,
                                            v_r_2874_,
                                        );
                                        v___x_2905_ = v_reuseFailAlloc_2906_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_2763_);
                        crate::leanh::lean_dec(v_k_2762_);
                        if v_isShared_2768_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2767_, 2, v_v_2759_);
                            crate::leanh::lean_ctor_set(v___x_2767_, 1, v_k_2758_);
                            v___x_2908_ = v___x_2767_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2909_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_size_2761_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_k_2758_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_v_2759_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 3, v_l_2764_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 4, v_r_2765_);
                            v___x_2908_ = v_reuseFailAlloc_2909_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_2761_);
                        v_impl_2910_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_2758_, v_v_2759_, v_r_2765_);
                        v___x_2911_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_2764_) == 0 {
                            v_size_2912_ = crate::leanh::lean_ctor_get(v_l_2764_, 0);
                            v_size_2913_ = crate::leanh::lean_ctor_get(v_impl_2910_, 0);
                            crate::leanh::lean_inc(v_size_2913_);
                            v_k_2914_ = crate::leanh::lean_ctor_get(v_impl_2910_, 1);
                            crate::leanh::lean_inc(v_k_2914_);
                            v_v_2915_ = crate::leanh::lean_ctor_get(v_impl_2910_, 2);
                            crate::leanh::lean_inc(v_v_2915_);
                            v_l_2916_ = crate::leanh::lean_ctor_get(v_impl_2910_, 3);
                            crate::leanh::lean_inc(v_l_2916_);
                            v_r_2917_ = crate::leanh::lean_ctor_get(v_impl_2910_, 4);
                            crate::leanh::lean_inc(v_r_2917_);
                            v___x_2918_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2919_ = lean_nat_mul(v___x_2918_, v_size_2912_);
                            v___x_2920_ = lean_nat_dec_lt(v___x_2919_, v_size_2913_);
                            crate::leanh::lean_dec(v___x_2919_);
                            if v___x_2920_ == 0 {
                                crate::leanh::lean_dec(v_r_2917_);
                                crate::leanh::lean_dec(v_l_2916_);
                                crate::leanh::lean_dec(v_v_2915_);
                                crate::leanh::lean_dec(v_k_2914_);
                                v___x_2921_ = lean_nat_add(v___x_2911_, v_size_2912_);
                                v___x_2922_ = lean_nat_add(v___x_2921_, v_size_2913_);
                                crate::leanh::lean_dec(v_size_2913_);
                                crate::leanh::lean_dec(v___x_2921_);
                                if v_isShared_2768_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2767_, 4, v_impl_2910_);
                                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2922_);
                                    v___x_2924_ = v___x_2767_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2925_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        0,
                                        v___x_2922_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        1,
                                        v_k_2762_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        2,
                                        v_v_2763_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        3,
                                        v_l_2764_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        4,
                                        v_impl_2910_,
                                    );
                                    v___x_2924_ = v_reuseFailAlloc_2925_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2989_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2910_)) as u8;
                                if v_isSharedCheck_2989_ == 0 {
                                    v_unused_2990_ = crate::leanh::lean_ctor_get(v_impl_2910_, 4);
                                    crate::leanh::lean_dec(v_unused_2990_);
                                    v_unused_2991_ = crate::leanh::lean_ctor_get(v_impl_2910_, 3);
                                    crate::leanh::lean_dec(v_unused_2991_);
                                    v_unused_2992_ = crate::leanh::lean_ctor_get(v_impl_2910_, 2);
                                    crate::leanh::lean_dec(v_unused_2992_);
                                    v_unused_2993_ = crate::leanh::lean_ctor_get(v_impl_2910_, 1);
                                    crate::leanh::lean_dec(v_unused_2993_);
                                    v_unused_2994_ = crate::leanh::lean_ctor_get(v_impl_2910_, 0);
                                    crate::leanh::lean_dec(v_unused_2994_);
                                    v___x_2927_ = v_impl_2910_;
                                    v_isShared_2928_ = v_isSharedCheck_2989_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2910_);
                                    v___x_2927_ = crate::leanh::lean_box(0);
                                    v_isShared_2928_ = v_isSharedCheck_2989_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2995_ = crate::leanh::lean_ctor_get(v_impl_2910_, 3);
                            crate::leanh::lean_inc(v_l_2995_);
                            if crate::leanh::lean_obj_tag(v_l_2995_) == 0 {
                                v_r_2996_ = crate::leanh::lean_ctor_get(v_impl_2910_, 4);
                                v_k_2997_ = crate::leanh::lean_ctor_get(v_impl_2910_, 1);
                                v_v_2998_ = crate::leanh::lean_ctor_get(v_impl_2910_, 2);
                                v_isSharedCheck_3021_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2910_)) as u8;
                                if v_isSharedCheck_3021_ == 0 {
                                    v_unused_3022_ = crate::leanh::lean_ctor_get(v_impl_2910_, 3);
                                    crate::leanh::lean_dec(v_unused_3022_);
                                    v_unused_3023_ = crate::leanh::lean_ctor_get(v_impl_2910_, 0);
                                    crate::leanh::lean_dec(v_unused_3023_);
                                    v___x_3000_ = v_impl_2910_;
                                    v_isShared_3001_ = v_isSharedCheck_3021_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2996_);
                                    crate::leanh::lean_inc(v_v_2998_);
                                    crate::leanh::lean_inc(v_k_2997_);
                                    crate::leanh::lean_dec(v_impl_2910_);
                                    v___x_3000_ = crate::leanh::lean_box(0);
                                    v_isShared_3001_ = v_isSharedCheck_3021_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3024_ = crate::leanh::lean_ctor_get(v_impl_2910_, 4);
                                crate::leanh::lean_inc(v_r_3024_);
                                if crate::leanh::lean_obj_tag(v_r_3024_) == 0 {
                                    v_k_3025_ = crate::leanh::lean_ctor_get(v_impl_2910_, 1);
                                    v_v_3026_ = crate::leanh::lean_ctor_get(v_impl_2910_, 2);
                                    v_isSharedCheck_3037_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2910_)) as u8;
                                    if v_isSharedCheck_3037_ == 0 {
                                        v_unused_3038_ =
                                            crate::leanh::lean_ctor_get(v_impl_2910_, 4);
                                        crate::leanh::lean_dec(v_unused_3038_);
                                        v_unused_3039_ =
                                            crate::leanh::lean_ctor_get(v_impl_2910_, 3);
                                        crate::leanh::lean_dec(v_unused_3039_);
                                        v_unused_3040_ =
                                            crate::leanh::lean_ctor_get(v_impl_2910_, 0);
                                        crate::leanh::lean_dec(v_unused_3040_);
                                        v___x_3028_ = v_impl_2910_;
                                        v_isShared_3029_ = v_isSharedCheck_3037_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_3026_);
                                        crate::leanh::lean_inc(v_k_3025_);
                                        crate::leanh::lean_dec(v_impl_2910_);
                                        v___x_3028_ = crate::leanh::lean_box(0);
                                        v_isShared_3029_ = v_isSharedCheck_3037_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3041_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2768_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2767_, 4, v_impl_2910_);
                                        crate::leanh::lean_ctor_set(v___x_2767_, 3, v_r_3024_);
                                        crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_3041_);
                                        v___x_3043_ = v___x_2767_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3044_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            0,
                                            v___x_3041_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            1,
                                            v_k_2762_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            2,
                                            v_v_2763_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            3,
                                            v_r_3024_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            4,
                                            v_impl_2910_,
                                        );
                                        v___x_3043_ = v_reuseFailAlloc_3044_;
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
                return v___x_2784_;
            }
            3 => {
                v_size_2789_ = crate::leanh::lean_ctor_get(v_l_2776_, 0);
                v_size_2790_ = crate::leanh::lean_ctor_get(v_r_2777_, 0);
                v_k_2791_ = crate::leanh::lean_ctor_get(v_r_2777_, 1);
                v_v_2792_ = crate::leanh::lean_ctor_get(v_r_2777_, 2);
                v_l_2793_ = crate::leanh::lean_ctor_get(v_r_2777_, 3);
                v_r_2794_ = crate::leanh::lean_ctor_get(v_r_2777_, 4);
                v___x_2795_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2796_ = lean_nat_mul(v___x_2795_, v_size_2789_);
                v___x_2797_ = lean_nat_dec_lt(v_size_2790_, v___x_2796_);
                crate::leanh::lean_dec(v___x_2796_);
                if v___x_2797_ == 0 {
                    crate::leanh::lean_inc(v_r_2794_);
                    crate::leanh::lean_inc(v_l_2793_);
                    crate::leanh::lean_inc(v_v_2792_);
                    crate::leanh::lean_inc(v_k_2791_);
                    v_isSharedCheck_2826_ = (!crate::leanh::lean_is_exclusive(v_r_2777_)) as u8;
                    if v_isSharedCheck_2826_ == 0 {
                        v_unused_2827_ = crate::leanh::lean_ctor_get(v_r_2777_, 4);
                        crate::leanh::lean_dec(v_unused_2827_);
                        v_unused_2828_ = crate::leanh::lean_ctor_get(v_r_2777_, 3);
                        crate::leanh::lean_dec(v_unused_2828_);
                        v_unused_2829_ = crate::leanh::lean_ctor_get(v_r_2777_, 2);
                        crate::leanh::lean_dec(v_unused_2829_);
                        v_unused_2830_ = crate::leanh::lean_ctor_get(v_r_2777_, 1);
                        crate::leanh::lean_dec(v_unused_2830_);
                        v_unused_2831_ = crate::leanh::lean_ctor_get(v_r_2777_, 0);
                        crate::leanh::lean_dec(v_unused_2831_);
                        v___x_2799_ = v_r_2777_;
                        v_isShared_2800_ = v_isSharedCheck_2826_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2777_);
                        v___x_2799_ = crate::leanh::lean_box(0);
                        v_isShared_2800_ = v_isSharedCheck_2826_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2767_);
                    v___x_2832_ = lean_nat_add(v___x_2771_, v_size_2773_);
                    crate::leanh::lean_dec(v_size_2773_);
                    v___x_2833_ = lean_nat_add(v___x_2832_, v_size_2772_);
                    crate::leanh::lean_dec(v___x_2832_);
                    v___x_2834_ = lean_nat_add(v___x_2771_, v_size_2772_);
                    v___x_2835_ = lean_nat_add(v___x_2834_, v_size_2790_);
                    crate::leanh::lean_dec(v___x_2834_);
                    crate::leanh::lean_inc_ref(v_r_2765_);
                    if v_isShared_2788_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2787_, 4, v_r_2765_);
                        crate::leanh::lean_ctor_set(v___x_2787_, 3, v_r_2777_);
                        crate::leanh::lean_ctor_set(v___x_2787_, 2, v_v_2763_);
                        crate::leanh::lean_ctor_set(v___x_2787_, 1, v_k_2762_);
                        crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2835_);
                        v___x_2837_ = v___x_2787_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2850_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2835_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_k_2762_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_v_2763_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_r_2777_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_r_2765_);
                        v___x_2837_ = v_reuseFailAlloc_2850_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2801_ = lean_nat_add(v___x_2771_, v_size_2773_);
                crate::leanh::lean_dec(v_size_2773_);
                v___x_2802_ = lean_nat_add(v___x_2801_, v_size_2772_);
                crate::leanh::lean_dec(v___x_2801_);
                v___x_2814_ = lean_nat_add(v___x_2771_, v_size_2789_);
                if crate::leanh::lean_obj_tag(v_l_2793_) == 0 {
                    v_size_2824_ = crate::leanh::lean_ctor_get(v_l_2793_, 0);
                    crate::leanh::lean_inc(v_size_2824_);
                    v___y_2816_ = v_size_2824_;
                    state = 8;
                    continue;
                } else {
                    v___x_2825_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2816_ = v___x_2825_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2807_ = lean_nat_add(v___y_2805_, v___y_2806_);
                crate::leanh::lean_dec(v___y_2806_);
                crate::leanh::lean_dec(v___y_2805_);
                if v_isShared_2800_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2799_, 4, v_r_2765_);
                    crate::leanh::lean_ctor_set(v___x_2799_, 3, v_r_2794_);
                    crate::leanh::lean_ctor_set(v___x_2799_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v___x_2799_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v___x_2799_, 0, v___x_2807_);
                    v___x_2809_ = v___x_2799_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_r_2794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_r_2765_);
                    v___x_2809_ = v_reuseFailAlloc_2813_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 4, v___x_2809_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 3, v___y_2804_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 2, v_v_2792_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v_k_2791_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2802_);
                    v___x_2811_ = v___x_2787_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2812_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_k_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_v_2792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 3, v___y_2804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 4, v___x_2809_);
                    v___x_2811_ = v_reuseFailAlloc_2812_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2811_;
            }
            8 => {
                v___x_2817_ = lean_nat_add(v___x_2814_, v___y_2816_);
                crate::leanh::lean_dec(v___y_2816_);
                crate::leanh::lean_dec(v___x_2814_);
                if v_isShared_2768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2767_, 4, v_l_2793_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 3, v_l_2776_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 2, v_v_2775_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 1, v_k_2774_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2817_);
                    v___x_2819_ = v___x_2767_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2823_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_k_2774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_v_2775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 3, v_l_2776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 4, v_l_2793_);
                    v___x_2819_ = v_reuseFailAlloc_2823_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2820_ = lean_nat_add(v___x_2771_, v_size_2772_);
                if crate::leanh::lean_obj_tag(v_r_2794_) == 0 {
                    v_size_2821_ = crate::leanh::lean_ctor_get(v_r_2794_, 0);
                    crate::leanh::lean_inc(v_size_2821_);
                    v___y_2804_ = v___x_2819_;
                    v___y_2805_ = v___x_2820_;
                    v___y_2806_ = v_size_2821_;
                    state = 5;
                    continue;
                } else {
                    v___x_2822_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2804_ = v___x_2819_;
                    v___y_2805_ = v___x_2820_;
                    v___y_2806_ = v___x_2822_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2844_ = (!crate::leanh::lean_is_exclusive(v_r_2765_)) as u8;
                if v_isSharedCheck_2844_ == 0 {
                    v_unused_2845_ = crate::leanh::lean_ctor_get(v_r_2765_, 4);
                    crate::leanh::lean_dec(v_unused_2845_);
                    v_unused_2846_ = crate::leanh::lean_ctor_get(v_r_2765_, 3);
                    crate::leanh::lean_dec(v_unused_2846_);
                    v_unused_2847_ = crate::leanh::lean_ctor_get(v_r_2765_, 2);
                    crate::leanh::lean_dec(v_unused_2847_);
                    v_unused_2848_ = crate::leanh::lean_ctor_get(v_r_2765_, 1);
                    crate::leanh::lean_dec(v_unused_2848_);
                    v_unused_2849_ = crate::leanh::lean_ctor_get(v_r_2765_, 0);
                    crate::leanh::lean_dec(v_unused_2849_);
                    v___x_2839_ = v_r_2765_;
                    v_isShared_2840_ = v_isSharedCheck_2844_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_2765_);
                    v___x_2839_ = crate::leanh::lean_box(0);
                    v_isShared_2840_ = v_isSharedCheck_2844_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2840_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2839_, 4, v___x_2837_);
                    crate::leanh::lean_ctor_set(v___x_2839_, 3, v_l_2776_);
                    crate::leanh::lean_ctor_set(v___x_2839_, 2, v_v_2775_);
                    crate::leanh::lean_ctor_set(v___x_2839_, 1, v_k_2774_);
                    crate::leanh::lean_ctor_set(v___x_2839_, 0, v___x_2833_);
                    v___x_2842_ = v___x_2839_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_k_2774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_v_2775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_l_2776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 4, v___x_2837_);
                    v___x_2842_ = v_reuseFailAlloc_2843_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2842_;
            }
            13 => {
                v___x_2864_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_2858_);
                if v_isShared_2863_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2862_, 3, v_r_2858_);
                    crate::leanh::lean_ctor_set(v___x_2862_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v___x_2862_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v___x_2862_, 0, v___x_2771_);
                    v___x_2866_ = v___x_2862_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2870_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_r_2858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_r_2858_);
                    v___x_2866_ = v_reuseFailAlloc_2870_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2767_, 4, v___x_2866_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 3, v_l_2857_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 2, v_v_2860_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 1, v_k_2859_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2864_);
                    v___x_2868_ = v___x_2767_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2864_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_k_2859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_v_2860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 3, v_l_2857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 4, v___x_2866_);
                    v___x_2868_ = v_reuseFailAlloc_2869_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2868_;
            }
            16 => {
                v_k_2880_ = crate::leanh::lean_ctor_get(v_r_2874_, 1);
                v_v_2881_ = crate::leanh::lean_ctor_get(v_r_2874_, 2);
                v_isSharedCheck_2895_ = (!crate::leanh::lean_is_exclusive(v_r_2874_)) as u8;
                if v_isSharedCheck_2895_ == 0 {
                    v_unused_2896_ = crate::leanh::lean_ctor_get(v_r_2874_, 4);
                    crate::leanh::lean_dec(v_unused_2896_);
                    v_unused_2897_ = crate::leanh::lean_ctor_get(v_r_2874_, 3);
                    crate::leanh::lean_dec(v_unused_2897_);
                    v_unused_2898_ = crate::leanh::lean_ctor_get(v_r_2874_, 0);
                    crate::leanh::lean_dec(v_unused_2898_);
                    v___x_2883_ = v_r_2874_;
                    v_isShared_2884_ = v_isSharedCheck_2895_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2881_);
                    crate::leanh::lean_inc(v_k_2880_);
                    crate::leanh::lean_dec(v_r_2874_);
                    v___x_2883_ = crate::leanh::lean_box(0);
                    v_isShared_2884_ = v_isSharedCheck_2895_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2885_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2884_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2883_, 4, v_l_2857_);
                    crate::leanh::lean_ctor_set(v___x_2883_, 3, v_l_2857_);
                    crate::leanh::lean_ctor_set(v___x_2883_, 2, v_v_2876_);
                    crate::leanh::lean_ctor_set(v___x_2883_, 1, v_k_2875_);
                    crate::leanh::lean_ctor_set(v___x_2883_, 0, v___x_2771_);
                    v___x_2887_ = v___x_2883_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_k_2875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_v_2876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 3, v_l_2857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 4, v_l_2857_);
                    v___x_2887_ = v_reuseFailAlloc_2894_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2878_, 4, v_l_2857_);
                    crate::leanh::lean_ctor_set(v___x_2878_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v___x_2878_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v___x_2878_, 0, v___x_2771_);
                    v___x_2889_ = v___x_2878_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 3, v_l_2857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 4, v_l_2857_);
                    v___x_2889_ = v_reuseFailAlloc_2893_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2767_, 4, v___x_2889_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 3, v___x_2887_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 2, v_v_2881_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 1, v_k_2880_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2885_);
                    v___x_2891_ = v___x_2767_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2892_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_k_2880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_v_2881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 3, v___x_2887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 4, v___x_2889_);
                    v___x_2891_ = v_reuseFailAlloc_2892_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2891_;
            }
            21 => {
                return v___x_2905_;
            }
            22 => {
                return v___x_2908_;
            }
            23 => {
                return v___x_2924_;
            }
            24 => {
                v_size_2929_ = crate::leanh::lean_ctor_get(v_l_2916_, 0);
                v_k_2930_ = crate::leanh::lean_ctor_get(v_l_2916_, 1);
                v_v_2931_ = crate::leanh::lean_ctor_get(v_l_2916_, 2);
                v_l_2932_ = crate::leanh::lean_ctor_get(v_l_2916_, 3);
                v_r_2933_ = crate::leanh::lean_ctor_get(v_l_2916_, 4);
                v_size_2934_ = crate::leanh::lean_ctor_get(v_r_2917_, 0);
                v___x_2935_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2936_ = lean_nat_mul(v___x_2935_, v_size_2934_);
                v___x_2937_ = lean_nat_dec_lt(v_size_2929_, v___x_2936_);
                crate::leanh::lean_dec(v___x_2936_);
                if v___x_2937_ == 0 {
                    crate::leanh::lean_inc(v_r_2933_);
                    crate::leanh::lean_inc(v_l_2932_);
                    crate::leanh::lean_inc(v_v_2931_);
                    crate::leanh::lean_inc(v_k_2930_);
                    v_isSharedCheck_2965_ = (!crate::leanh::lean_is_exclusive(v_l_2916_)) as u8;
                    if v_isSharedCheck_2965_ == 0 {
                        v_unused_2966_ = crate::leanh::lean_ctor_get(v_l_2916_, 4);
                        crate::leanh::lean_dec(v_unused_2966_);
                        v_unused_2967_ = crate::leanh::lean_ctor_get(v_l_2916_, 3);
                        crate::leanh::lean_dec(v_unused_2967_);
                        v_unused_2968_ = crate::leanh::lean_ctor_get(v_l_2916_, 2);
                        crate::leanh::lean_dec(v_unused_2968_);
                        v_unused_2969_ = crate::leanh::lean_ctor_get(v_l_2916_, 1);
                        crate::leanh::lean_dec(v_unused_2969_);
                        v_unused_2970_ = crate::leanh::lean_ctor_get(v_l_2916_, 0);
                        crate::leanh::lean_dec(v_unused_2970_);
                        v___x_2939_ = v_l_2916_;
                        v_isShared_2940_ = v_isSharedCheck_2965_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_2916_);
                        v___x_2939_ = crate::leanh::lean_box(0);
                        v_isShared_2940_ = v_isSharedCheck_2965_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2767_);
                    v___x_2971_ = lean_nat_add(v___x_2911_, v_size_2912_);
                    v___x_2972_ = lean_nat_add(v___x_2971_, v_size_2913_);
                    crate::leanh::lean_dec(v_size_2913_);
                    v___x_2973_ = lean_nat_add(v___x_2971_, v_size_2929_);
                    crate::leanh::lean_dec(v___x_2971_);
                    crate::leanh::lean_inc_ref(v_l_2764_);
                    if v_isShared_2928_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2927_, 4, v_l_2916_);
                        crate::leanh::lean_ctor_set(v___x_2927_, 3, v_l_2764_);
                        crate::leanh::lean_ctor_set(v___x_2927_, 2, v_v_2763_);
                        crate::leanh::lean_ctor_set(v___x_2927_, 1, v_k_2762_);
                        crate::leanh::lean_ctor_set(v___x_2927_, 0, v___x_2973_);
                        v___x_2975_ = v___x_2927_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2988_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2973_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_k_2762_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_v_2763_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 3, v_l_2764_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 4, v_l_2916_);
                        v___x_2975_ = v_reuseFailAlloc_2988_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2941_ = lean_nat_add(v___x_2911_, v_size_2912_);
                v___x_2942_ = lean_nat_add(v___x_2941_, v_size_2913_);
                crate::leanh::lean_dec(v_size_2913_);
                if crate::leanh::lean_obj_tag(v_l_2932_) == 0 {
                    v_size_2963_ = crate::leanh::lean_ctor_get(v_l_2932_, 0);
                    crate::leanh::lean_inc(v_size_2963_);
                    v___y_2955_ = v_size_2963_;
                    state = 29;
                    continue;
                } else {
                    v___x_2964_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2955_ = v___x_2964_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2947_ = lean_nat_add(v___y_2945_, v___y_2946_);
                crate::leanh::lean_dec(v___y_2946_);
                crate::leanh::lean_dec(v___y_2945_);
                if v_isShared_2940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2939_, 4, v_r_2917_);
                    crate::leanh::lean_ctor_set(v___x_2939_, 3, v_r_2933_);
                    crate::leanh::lean_ctor_set(v___x_2939_, 2, v_v_2915_);
                    crate::leanh::lean_ctor_set(v___x_2939_, 1, v_k_2914_);
                    crate::leanh::lean_ctor_set(v___x_2939_, 0, v___x_2947_);
                    v___x_2949_ = v___x_2939_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_k_2914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_v_2915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_r_2933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_r_2917_);
                    v___x_2949_ = v_reuseFailAlloc_2953_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2928_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2927_, 4, v___x_2949_);
                    crate::leanh::lean_ctor_set(v___x_2927_, 3, v___y_2944_);
                    crate::leanh::lean_ctor_set(v___x_2927_, 2, v_v_2931_);
                    crate::leanh::lean_ctor_set(v___x_2927_, 1, v_k_2930_);
                    crate::leanh::lean_ctor_set(v___x_2927_, 0, v___x_2942_);
                    v___x_2951_ = v___x_2927_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2952_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_k_2930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 2, v_v_2931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 3, v___y_2944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 4, v___x_2949_);
                    v___x_2951_ = v_reuseFailAlloc_2952_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2951_;
            }
            29 => {
                v___x_2956_ = lean_nat_add(v___x_2941_, v___y_2955_);
                crate::leanh::lean_dec(v___y_2955_);
                crate::leanh::lean_dec(v___x_2941_);
                if v_isShared_2768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2767_, 4, v_l_2932_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2956_);
                    v___x_2958_ = v___x_2767_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2962_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 3, v_l_2764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 4, v_l_2932_);
                    v___x_2958_ = v_reuseFailAlloc_2962_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2959_ = lean_nat_add(v___x_2911_, v_size_2934_);
                if crate::leanh::lean_obj_tag(v_r_2933_) == 0 {
                    v_size_2960_ = crate::leanh::lean_ctor_get(v_r_2933_, 0);
                    crate::leanh::lean_inc(v_size_2960_);
                    v___y_2944_ = v___x_2958_;
                    v___y_2945_ = v___x_2959_;
                    v___y_2946_ = v_size_2960_;
                    state = 26;
                    continue;
                } else {
                    v___x_2961_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2944_ = v___x_2958_;
                    v___y_2945_ = v___x_2959_;
                    v___y_2946_ = v___x_2961_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2982_ = (!crate::leanh::lean_is_exclusive(v_l_2764_)) as u8;
                if v_isSharedCheck_2982_ == 0 {
                    v_unused_2983_ = crate::leanh::lean_ctor_get(v_l_2764_, 4);
                    crate::leanh::lean_dec(v_unused_2983_);
                    v_unused_2984_ = crate::leanh::lean_ctor_get(v_l_2764_, 3);
                    crate::leanh::lean_dec(v_unused_2984_);
                    v_unused_2985_ = crate::leanh::lean_ctor_get(v_l_2764_, 2);
                    crate::leanh::lean_dec(v_unused_2985_);
                    v_unused_2986_ = crate::leanh::lean_ctor_get(v_l_2764_, 1);
                    crate::leanh::lean_dec(v_unused_2986_);
                    v_unused_2987_ = crate::leanh::lean_ctor_get(v_l_2764_, 0);
                    crate::leanh::lean_dec(v_unused_2987_);
                    v___x_2977_ = v_l_2764_;
                    v_isShared_2978_ = v_isSharedCheck_2982_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_2764_);
                    v___x_2977_ = crate::leanh::lean_box(0);
                    v_isShared_2978_ = v_isSharedCheck_2982_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2977_, 4, v_r_2917_);
                    crate::leanh::lean_ctor_set(v___x_2977_, 3, v___x_2975_);
                    crate::leanh::lean_ctor_set(v___x_2977_, 2, v_v_2915_);
                    crate::leanh::lean_ctor_set(v___x_2977_, 1, v_k_2914_);
                    crate::leanh::lean_ctor_set(v___x_2977_, 0, v___x_2972_);
                    v___x_2980_ = v___x_2977_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_k_2914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_v_2915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 3, v___x_2975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 4, v_r_2917_);
                    v___x_2980_ = v_reuseFailAlloc_2981_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2980_;
            }
            34 => {
                v_k_3002_ = crate::leanh::lean_ctor_get(v_l_2995_, 1);
                v_v_3003_ = crate::leanh::lean_ctor_get(v_l_2995_, 2);
                v_isSharedCheck_3017_ = (!crate::leanh::lean_is_exclusive(v_l_2995_)) as u8;
                if v_isSharedCheck_3017_ == 0 {
                    v_unused_3018_ = crate::leanh::lean_ctor_get(v_l_2995_, 4);
                    crate::leanh::lean_dec(v_unused_3018_);
                    v_unused_3019_ = crate::leanh::lean_ctor_get(v_l_2995_, 3);
                    crate::leanh::lean_dec(v_unused_3019_);
                    v_unused_3020_ = crate::leanh::lean_ctor_get(v_l_2995_, 0);
                    crate::leanh::lean_dec(v_unused_3020_);
                    v___x_3005_ = v_l_2995_;
                    v_isShared_3006_ = v_isSharedCheck_3017_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3003_);
                    crate::leanh::lean_inc(v_k_3002_);
                    crate::leanh::lean_dec(v_l_2995_);
                    v___x_3005_ = crate::leanh::lean_box(0);
                    v_isShared_3006_ = v_isSharedCheck_3017_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3007_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_2996_, 2);
                if v_isShared_3006_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3005_, 4, v_r_2996_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 3, v_r_2996_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 0, v___x_2911_);
                    v___x_3009_ = v___x_3005_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3016_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_2911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 3, v_r_2996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 4, v_r_2996_);
                    v___x_3009_ = v_reuseFailAlloc_3016_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_2996_);
                if v_isShared_3001_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3000_, 3, v_r_2996_);
                    crate::leanh::lean_ctor_set(v___x_3000_, 0, v___x_2911_);
                    v___x_3011_ = v___x_3000_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3015_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_2911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 1, v_k_2997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 2, v_v_2998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 3, v_r_2996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 4, v_r_2996_);
                    v___x_3011_ = v_reuseFailAlloc_3015_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2767_, 4, v___x_3011_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 3, v___x_3009_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 2, v_v_3003_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 1, v_k_3002_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_3007_);
                    v___x_3013_ = v___x_2767_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_k_3002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_v_3003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 3, v___x_3009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 4, v___x_3011_);
                    v___x_3013_ = v_reuseFailAlloc_3014_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3013_;
            }
            39 => {
                v___x_3030_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3029_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3028_, 4, v_l_2995_);
                    crate::leanh::lean_ctor_set(v___x_3028_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v___x_3028_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v___x_3028_, 0, v___x_2911_);
                    v___x_3032_ = v___x_3028_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_2911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_2762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_2763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_l_2995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_l_2995_);
                    v___x_3032_ = v_reuseFailAlloc_3036_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2767_, 4, v_r_3024_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 3, v___x_3032_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 2, v_v_3026_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 1, v_k_3025_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_3030_);
                    v___x_3034_ = v___x_2767_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_k_3025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_v_3026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 3, v___x_3032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 4, v_r_3024_);
                    v___x_3034_ = v_reuseFailAlloc_3035_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3034_;
            }
            42 => {
                return v___x_3043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_LeanExe_initFacetConfigs___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = crate::leanh::lean_box(1);
    v___x_3049_ = l_Lake_LeanExe_defaultFacetConfig;
    v___x_3050_ = l_Lake_LeanExe_defaultFacet;
    v___x_3051_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(
            v___x_3050_,
            v___x_3049_,
            v___x_3048_,
        );
    return v___x_3051_;
}
pub unsafe fn _init_l_Lake_LeanExe_initFacetConfigs___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3052_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExe_initFacetConfigs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExe_initFacetConfigs___closed__0_once),
        _init_l_Lake_LeanExe_initFacetConfigs___closed__0,
    );
    v___x_3053_ = l_Lake_LeanExe_exeFacetConfig;
    v___x_3054_ = l_Lake_LeanExe_exeFacet;
    v___x_3055_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(
            v___x_3054_,
            v___x_3053_,
            v___x_3052_,
        );
    return v___x_3055_;
}
pub unsafe fn _init_l_Lake_LeanExe_initFacetConfigs() -> *mut crate::leanh::LeanObject {
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3056_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExe_initFacetConfigs___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanExe_initFacetConfigs___closed__1_once),
        _init_l_Lake_LeanExe_initFacetConfigs___closed__1,
    );
    return v___x_3056_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(
    mut v_00_u03b2_3057_: *mut crate::leanh::LeanObject,
    mut v_k_3058_: *mut crate::leanh::LeanObject,
    mut v_v_3059_: *mut crate::leanh::LeanObject,
    mut v_t_3060_: *mut crate::leanh::LeanObject,
    mut v_hl_3061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3062_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(
            v_k_3058_, v_v_3059_, v_t_3060_,
        );
    return v___x_3062_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Executable(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_FacetConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Register(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Target_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Common(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13 = _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13();
    crate::leanh::lean_mark_persistent(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13);
    l_Lake_LeanExe_exeFacetConfig = _init_l_Lake_LeanExe_exeFacetConfig();
    crate::leanh::lean_mark_persistent(l_Lake_LeanExe_exeFacetConfig);
    l_Lake_LeanExe_defaultFacetConfig = _init_l_Lake_LeanExe_defaultFacetConfig();
    crate::leanh::lean_mark_persistent(l_Lake_LeanExe_defaultFacetConfig);
    l_Lake_LeanExe_initFacetConfigs = _init_l_Lake_LeanExe_initFacetConfigs();
    crate::leanh::lean_mark_persistent(l_Lake_LeanExe_initFacetConfigs);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Executable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Executable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_FacetConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Register(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Target_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Common(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Executable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Executable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Executable(builtin);
}
