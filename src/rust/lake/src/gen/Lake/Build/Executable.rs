// Lean compiler output
// Module: Lake.Build.Executable
// Imports: Lake.Config.FacetConfig Lake.Build.Job.Register Lake.Build.Target.Fetch Lake.Build.Common Lake.Build.Infos
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_io_wait, lean_mk_array, lean_name_eq,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_st_ref_set,
    lean_st_ref_take, lean_strict_and, lean_string_append, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
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
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [39, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [39, 44, 32, 103, 111, 116, 32, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [117, 110, 107, 110, 111, 119, 110, 0]};
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0: u64 = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 110, 105, 108, 62, 0]};
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [98, 97, 100, 32, 105, 109, 112, 111, 114, 116, 115, 32, 40, 115, 101, 101, 32, 116, 104, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [39, 32, 106, 111, 98, 32, 102, 111, 114, 32, 100, 101, 116, 97, 105, 108, 115, 41, 0]};
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0_value:
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
static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut leanh::LeanObject)],
};
pub static mut l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1_value
) as *mut leanh::LeanObject;
pub static l_Lake_LeanExe_exeFacetConfig___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
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
static mut l_Lake_LeanExe_exeFacetConfig___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_exeFacetConfig___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExe_exeFacetConfig___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
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
static mut l_Lake_LeanExe_exeFacetConfig___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_exeFacetConfig___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExe_exeFacetConfig___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExe_exeFacetConfig___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExe_exeFacetConfig: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExe_defaultFacetConfig___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
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
static mut l_Lake_LeanExe_defaultFacetConfig___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_defaultFacetConfig___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExe_defaultFacetConfig___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExe_defaultFacetConfig___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExe_defaultFacetConfig: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanExe_initFacetConfigs___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExe_initFacetConfigs___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanExe_initFacetConfigs___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExe_initFacetConfigs___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExe_initFacetConfigs: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1534_: u8 = 0;
    let mut v_name_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = 1;
    v_name_1535_ = l_Lake_instDataKindDynlib;
    v___x_1536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_1535_,
        v___x_1534_,
    );
    return v___x_1536_;
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(
    mut v_defaultPkg_1540_: *mut leanh::LeanObject,
    mut v_self_1541_: *mut leanh::LeanObject,
    mut v_a_1542_: *mut leanh::LeanObject,
    mut v_a_1543_: *mut leanh::LeanObject,
    mut v_a_1544_: *mut leanh::LeanObject,
    mut v_a_1545_: *mut leanh::LeanObject,
    mut v_a_1546_: *mut leanh::LeanObject,
    mut v_a_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v_a_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v_kind_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: u8 = 0;
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_unused_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut v_unused_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1599_: u8 = 0;
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1549_ = 1;
                leanh::lean_inc_ref_n(v_self_1541_, 2);
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
                if leanh::lean_obj_tag(v___x_1550_) == 0 {
                    v_a_1551_ = leanh::lean_ctor_get(v___x_1550_, 0);
                    leanh::lean_inc(v_a_1551_);
                    v_snd_1552_ = leanh::lean_ctor_get(v_a_1551_, 1);
                    v_isSharedCheck_1593_ = (!leanh::lean_is_exclusive(v_a_1551_)) as u8;
                    if v_isSharedCheck_1593_ == 0 {
                        v_unused_1594_ = leanh::lean_ctor_get(v_a_1551_, 0);
                        leanh::lean_dec(v_unused_1594_);
                        v___x_1554_ = v_a_1551_;
                        v_isShared_1555_ = v_isSharedCheck_1593_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1552_);
                        leanh::lean_dec(v_a_1551_);
                        v___x_1554_ = leanh::lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1593_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_self_1541_);
                    v_a_1595_ = leanh::lean_ctor_get(v___x_1550_, 0);
                    v_a_1596_ = leanh::lean_ctor_get(v___x_1550_, 1);
                    v_isSharedCheck_1603_ = (!leanh::lean_is_exclusive(v___x_1550_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1598_ = v___x_1550_;
                        v_isShared_1599_ = v_isSharedCheck_1603_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1596_);
                        leanh::lean_inc(v_a_1595_);
                        leanh::lean_dec(v___x_1550_);
                        v___x_1598_ = leanh::lean_box(0);
                        v_isShared_1599_ = v_isSharedCheck_1603_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1556_ = leanh::lean_ctor_get(v___x_1550_, 1);
                v_isSharedCheck_1591_ = (!leanh::lean_is_exclusive(v___x_1550_)) as u8;
                if v_isSharedCheck_1591_ == 0 {
                    v_unused_1592_ = leanh::lean_ctor_get(v___x_1550_, 0);
                    leanh::lean_dec(v_unused_1592_);
                    v___x_1558_ = v___x_1550_;
                    v_isShared_1559_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1556_);
                    leanh::lean_dec(v___x_1550_);
                    v___x_1558_ = leanh::lean_box(0);
                    v_isShared_1559_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_kind_1560_ = leanh::lean_ctor_get(v_snd_1552_, 1);
                v_name_1561_ = l_Lake_instDataKindDynlib;
                v___x_1581_ = lean_name_eq(v_kind_1560_, v_name_1561_);
                if v___x_1581_ == 0 {
                    leanh::lean_inc(v_kind_1560_);
                    leanh::lean_del_object(v___x_1554_);
                    leanh::lean_dec(v_snd_1552_);
                    v___x_1582_ = l_Lean_Name_isAnonymous(v_kind_1560_);
                    if v___x_1582_ == 0 {
                        v___x_1583_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4;
                        v___x_1584_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_1560_,
                                v___x_1549_,
                            );
                        v___x_1585_ = lean_string_append(v___x_1583_, v___x_1584_);
                        leanh::lean_dec_ref(v___x_1584_);
                        v___x_1586_ = lean_string_append(v___x_1585_, v___x_1583_);
                        v___y_1563_ = v___x_1586_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_kind_1560_);
                        v___x_1587_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5;
                        v___y_1563_ = v___x_1587_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1558_);
                    leanh::lean_dec_ref(v_self_1541_);
                    if v_isShared_1555_ == 0 {
                        leanh::lean_ctor_set(v___x_1554_, 1, v_a_1556_);
                        leanh::lean_ctor_set(v___x_1554_, 0, v_snd_1552_);
                        v___x_1589_ = v___x_1554_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1590_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_snd_1552_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_a_1556_);
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
                leanh::lean_dec_ref(v___x_1565_);
                v___x_1567_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1;
                v___x_1568_ = lean_string_append(v___x_1566_, v___x_1567_);
                v___x_1569_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2_once), _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2);
                v___x_1570_ = lean_string_append(v___x_1568_, v___x_1569_);
                v___x_1571_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3;
                v___x_1572_ = lean_string_append(v___x_1570_, v___x_1571_);
                v___x_1573_ = lean_string_append(v___x_1572_, v___y_1563_);
                leanh::lean_dec_ref(v___y_1563_);
                v___x_1574_ = 3;
                v___x_1575_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1575_, 0, v___x_1573_);
                leanh::lean_ctor_set_uint8(
                    v___x_1575_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1574_,
                );
                v___x_1576_ = lean_array_get_size(v_a_1556_);
                v___x_1577_ = lean_array_push(v_a_1556_, v___x_1575_);
                if v_isShared_1559_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1558_, 1);
                    leanh::lean_ctor_set(v___x_1558_, 1, v___x_1577_);
                    leanh::lean_ctor_set(v___x_1558_, 0, v___x_1576_);
                    v___x_1579_ = v___x_1558_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 1, v___x_1577_);
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
                    v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1595_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_a_1596_);
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
    mut v_defaultPkg_1604_: *mut leanh::LeanObject,
    mut v_self_1605_: *mut leanh::LeanObject,
    mut v_a_1606_: *mut leanh::LeanObject,
    mut v_a_1607_: *mut leanh::LeanObject,
    mut v_a_1608_: *mut leanh::LeanObject,
    mut v_a_1609_: *mut leanh::LeanObject,
    mut v_a_1610_: *mut leanh::LeanObject,
    mut v_a_1611_: *mut leanh::LeanObject,
    mut v_a_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(v_defaultPkg_1604_, v_self_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
    leanh::lean_dec_ref(v_a_1610_);
    leanh::lean_dec(v_a_1609_);
    leanh::lean_dec(v_a_1608_);
    leanh::lean_dec(v_a_1607_);
    return v_res_1613_;
}
pub unsafe fn _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1614_: u8 = 0;
    let mut v_name_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = 1;
    v_name_1615_ = l_Lake_instDataKindFilePath;
    v___x_1616_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_1615_,
        v___x_1614_,
    );
    return v___x_1616_;
}
pub unsafe fn l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(
    mut v_defaultPkg_1617_: *mut leanh::LeanObject,
    mut v_self_1618_: *mut leanh::LeanObject,
    mut v_a_1619_: *mut leanh::LeanObject,
    mut v_a_1620_: *mut leanh::LeanObject,
    mut v_a_1621_: *mut leanh::LeanObject,
    mut v_a_1622_: *mut leanh::LeanObject,
    mut v_a_1623_: *mut leanh::LeanObject,
    mut v_a_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1632_: u8 = 0;
    let mut v_a_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1636_: u8 = 0;
    let mut v_kind_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v_unused_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1670_: u8 = 0;
    let mut v_unused_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1626_ = 1;
                leanh::lean_inc_ref_n(v_self_1618_, 2);
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
                if leanh::lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = leanh::lean_ctor_get(v___x_1627_, 0);
                    leanh::lean_inc(v_a_1628_);
                    v_snd_1629_ = leanh::lean_ctor_get(v_a_1628_, 1);
                    v_isSharedCheck_1670_ = (!leanh::lean_is_exclusive(v_a_1628_)) as u8;
                    if v_isSharedCheck_1670_ == 0 {
                        v_unused_1671_ = leanh::lean_ctor_get(v_a_1628_, 0);
                        leanh::lean_dec(v_unused_1671_);
                        v___x_1631_ = v_a_1628_;
                        v_isShared_1632_ = v_isSharedCheck_1670_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1629_);
                        leanh::lean_dec(v_a_1628_);
                        v___x_1631_ = leanh::lean_box(0);
                        v_isShared_1632_ = v_isSharedCheck_1670_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_self_1618_);
                    v_a_1672_ = leanh::lean_ctor_get(v___x_1627_, 0);
                    v_a_1673_ = leanh::lean_ctor_get(v___x_1627_, 1);
                    v_isSharedCheck_1680_ = (!leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1680_ == 0 {
                        v___x_1675_ = v___x_1627_;
                        v_isShared_1676_ = v_isSharedCheck_1680_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1673_);
                        leanh::lean_inc(v_a_1672_);
                        leanh::lean_dec(v___x_1627_);
                        v___x_1675_ = leanh::lean_box(0);
                        v_isShared_1676_ = v_isSharedCheck_1680_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1633_ = leanh::lean_ctor_get(v___x_1627_, 1);
                v_isSharedCheck_1668_ = (!leanh::lean_is_exclusive(v___x_1627_)) as u8;
                if v_isSharedCheck_1668_ == 0 {
                    v_unused_1669_ = leanh::lean_ctor_get(v___x_1627_, 0);
                    leanh::lean_dec(v_unused_1669_);
                    v___x_1635_ = v___x_1627_;
                    v_isShared_1636_ = v_isSharedCheck_1668_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1633_);
                    leanh::lean_dec(v___x_1627_);
                    v___x_1635_ = leanh::lean_box(0);
                    v_isShared_1636_ = v_isSharedCheck_1668_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_kind_1637_ = leanh::lean_ctor_get(v_snd_1629_, 1);
                v_name_1638_ = l_Lake_instDataKindFilePath;
                v___x_1658_ = lean_name_eq(v_kind_1637_, v_name_1638_);
                if v___x_1658_ == 0 {
                    leanh::lean_inc(v_kind_1637_);
                    leanh::lean_del_object(v___x_1631_);
                    leanh::lean_dec(v_snd_1629_);
                    v___x_1659_ = l_Lean_Name_isAnonymous(v_kind_1637_);
                    if v___x_1659_ == 0 {
                        v___x_1660_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4;
                        v___x_1661_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_1637_,
                                v___x_1626_,
                            );
                        v___x_1662_ = lean_string_append(v___x_1660_, v___x_1661_);
                        leanh::lean_dec_ref(v___x_1661_);
                        v___x_1663_ = lean_string_append(v___x_1662_, v___x_1660_);
                        v___y_1640_ = v___x_1663_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_kind_1637_);
                        v___x_1664_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5;
                        v___y_1640_ = v___x_1664_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1635_);
                    leanh::lean_dec_ref(v_self_1618_);
                    if v_isShared_1632_ == 0 {
                        leanh::lean_ctor_set(v___x_1631_, 1, v_a_1633_);
                        leanh::lean_ctor_set(v___x_1631_, 0, v_snd_1629_);
                        v___x_1666_ = v___x_1631_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1667_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_snd_1629_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_a_1633_);
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
                leanh::lean_dec_ref(v___x_1642_);
                v___x_1644_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1;
                v___x_1645_ = lean_string_append(v___x_1643_, v___x_1644_);
                v___x_1646_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0_once), _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0);
                v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
                v___x_1648_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3;
                v___x_1649_ = lean_string_append(v___x_1647_, v___x_1648_);
                v___x_1650_ = lean_string_append(v___x_1649_, v___y_1640_);
                leanh::lean_dec_ref(v___y_1640_);
                v___x_1651_ = 3;
                v___x_1652_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1652_, 0, v___x_1650_);
                leanh::lean_ctor_set_uint8(
                    v___x_1652_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1651_,
                );
                v___x_1653_ = lean_array_get_size(v_a_1633_);
                v___x_1654_ = lean_array_push(v_a_1633_, v___x_1652_);
                if v_isShared_1636_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1635_, 1);
                    leanh::lean_ctor_set(v___x_1635_, 1, v___x_1654_);
                    leanh::lean_ctor_set(v___x_1635_, 0, v___x_1653_);
                    v___x_1656_ = v___x_1635_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1654_);
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
                    v_reuseFailAlloc_1679_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_a_1673_);
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
    mut v_defaultPkg_1681_: *mut leanh::LeanObject,
    mut v_self_1682_: *mut leanh::LeanObject,
    mut v_a_1683_: *mut leanh::LeanObject,
    mut v_a_1684_: *mut leanh::LeanObject,
    mut v_a_1685_: *mut leanh::LeanObject,
    mut v_a_1686_: *mut leanh::LeanObject,
    mut v_a_1687_: *mut leanh::LeanObject,
    mut v_a_1688_: *mut leanh::LeanObject,
    mut v_a_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1690_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(v_defaultPkg_1681_, v_self_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
    leanh::lean_dec_ref(v_a_1687_);
    leanh::lean_dec(v_a_1686_);
    leanh::lean_dec(v_a_1685_);
    leanh::lean_dec(v_a_1684_);
    return v_res_1690_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = leanh::lean_box(0);
    v___x_1692_ = leanh::lean_unsigned_to_nat(16);
    v___x_1693_ = lean_mk_array(v___x_1692_, v___x_1691_);
    return v___x_1693_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0);
    v___x_1695_ = leanh::lean_unsigned_to_nat(0);
    v___x_1696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
    leanh::lean_ctor_set(v___x_1696_, 1, v___x_1694_);
    return v___x_1696_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2;
    v___x_1700_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1);
    v___x_1701_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1701_, 0, v___x_1700_);
    leanh::lean_ctor_set(v___x_1701_, 1, v___x_1699_);
    return v___x_1701_;
}
pub unsafe fn _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13()
-> *mut leanh::LeanObject {
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3), core::ptr::addr_of_mut!(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3_once), _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3);
    return v___x_1702_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0()
-> u64 {
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u64 = 0;
    v___x_1703_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1704_ = lean_uint64_of_nat(v___x_1703_);
    return v___x_1704_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(
    mut v_x_1705_: *mut leanh::LeanObject,
    mut v_x_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v_name_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u64 = 0;
    let mut v_hash_1735_: u64 = 0;
    let mut v_isSharedCheck_1736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1706_) == 0 {
                    return v_x_1705_;
                } else {
                    v_key_1707_ = leanh::lean_ctor_get(v_x_1706_, 0);
                    v_value_1708_ = leanh::lean_ctor_get(v_x_1706_, 1);
                    v_tail_1709_ = leanh::lean_ctor_get(v_x_1706_, 2);
                    v_isSharedCheck_1736_ = (!leanh::lean_is_exclusive(v_x_1706_)) as u8;
                    if v_isSharedCheck_1736_ == 0 {
                        v___x_1711_ = v_x_1706_;
                        v_isShared_1712_ = v_isSharedCheck_1736_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1709_);
                        leanh::lean_inc(v_value_1708_);
                        leanh::lean_inc(v_key_1707_);
                        leanh::lean_dec(v_x_1706_);
                        v___x_1711_ = leanh::lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1736_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_1713_ = leanh::lean_ctor_get(v_key_1707_, 1);
                v___x_1714_ = lean_array_get_size(v_x_1705_);
                if leanh::lean_obj_tag(v_name_1713_) == 0 {
                    v___x_1734_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
                    v___y_1716_ = v___x_1734_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1735_ = leanh::lean_ctor_get_uint64(
                        v_name_1713_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                leanh::lean_inc(v___x_1728_);
                if v_isShared_1712_ == 0 {
                    leanh::lean_ctor_set(v___x_1711_, 2, v___x_1728_);
                    v___x_1730_ = v___x_1711_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1733_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_key_1707_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_value_1708_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 2, v___x_1728_);
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
    mut v_i_1737_: *mut leanh::LeanObject,
    mut v_source_1738_: *mut leanh::LeanObject,
    mut v_target_1739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: u8 = 0;
    let mut v_es_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1740_ = lean_array_get_size(v_source_1738_);
                v___x_1741_ = lean_nat_dec_lt(v_i_1737_, v___x_1740_);
                if v___x_1741_ == 0 {
                    leanh::lean_dec_ref(v_source_1738_);
                    leanh::lean_dec(v_i_1737_);
                    return v_target_1739_;
                } else {
                    v_es_1742_ = lean_array_fget(v_source_1738_, v_i_1737_);
                    v___x_1743_ = leanh::lean_box(0);
                    v_source_1744_ = lean_array_fset(v_source_1738_, v_i_1737_, v___x_1743_);
                    v_target_1745_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(v_target_1739_, v_es_1742_);
                    v___x_1746_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1747_ = lean_nat_add(v_i_1737_, v___x_1746_);
                    leanh::lean_dec(v_i_1737_);
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
    mut v_data_1749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = lean_array_get_size(v_data_1749_);
    v___x_1751_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1752_ = lean_nat_mul(v___x_1750_, v___x_1751_);
    v___x_1753_ = leanh::lean_unsigned_to_nat(0);
    v___x_1754_ = leanh::lean_box(0);
    v___x_1755_ = lean_mk_array(v_nbuckets_1752_, v___x_1754_);
    v___x_1756_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(v___x_1753_, v_data_1749_, v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(
    mut v_a_1757_: *mut leanh::LeanObject,
    mut v_x_1758_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1759_: u8 = 0;
    let mut v_key_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1758_) == 0 {
                    v___x_1759_ = 0;
                    return v___x_1759_;
                } else {
                    v_key_1760_ = leanh::lean_ctor_get(v_x_1758_, 0);
                    v_tail_1761_ = leanh::lean_ctor_get(v_x_1758_, 2);
                    v_name_1762_ = leanh::lean_ctor_get(v_key_1760_, 1);
                    v_name_1763_ = leanh::lean_ctor_get(v_a_1757_, 1);
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
    mut v_a_1766_: *mut leanh::LeanObject,
    mut v_x_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1768_: u8 = 0;
    let mut v_r_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(v_a_1766_, v_x_1767_);
    leanh::lean_dec(v_x_1767_);
    leanh::lean_dec_ref(v_a_1766_);
    v_r_1769_ = leanh::lean_box((v_res_1768_) as usize);
    return v_r_1769_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(
    mut v_m_1770_: *mut leanh::LeanObject,
    mut v_a_1771_: *mut leanh::LeanObject,
    mut v_b_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v_val_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u64 = 0;
    let mut v_hash_1816_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1773_ = leanh::lean_ctor_get(v_m_1770_, 0);
                v_buckets_1774_ = leanh::lean_ctor_get(v_m_1770_, 1);
                v_name_1775_ = leanh::lean_ctor_get(v_a_1771_, 1);
                v___x_1776_ = lean_array_get_size(v_buckets_1774_);
                if leanh::lean_obj_tag(v_name_1775_) == 0 {
                    v___x_1815_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
                    v___y_1778_ = v___x_1815_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1816_ = leanh::lean_ctor_get_uint64(
                        v_name_1775_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                    leanh::lean_inc_ref(v_buckets_1774_);
                    leanh::lean_inc(v_size_1773_);
                    v_isSharedCheck_1812_ = (!leanh::lean_is_exclusive(v_m_1770_)) as u8;
                    if v_isSharedCheck_1812_ == 0 {
                        v_unused_1813_ = leanh::lean_ctor_get(v_m_1770_, 1);
                        leanh::lean_dec(v_unused_1813_);
                        v_unused_1814_ = leanh::lean_ctor_get(v_m_1770_, 0);
                        leanh::lean_dec(v_unused_1814_);
                        v___x_1793_ = v_m_1770_;
                        v_isShared_1794_ = v_isSharedCheck_1812_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_1770_);
                        v___x_1793_ = leanh::lean_box(0);
                        v_isShared_1794_ = v_isSharedCheck_1812_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_1772_);
                    leanh::lean_dec_ref(v_a_1771_);
                    return v_m_1770_;
                }
            }
            2 => {
                v___x_1795_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_1796_ = lean_nat_add(v_size_1773_, v___x_1795_);
                leanh::lean_dec(v_size_1773_);
                leanh::lean_inc(v_bkt_1790_);
                v___x_1797_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1797_, 0, v_a_1771_);
                leanh::lean_ctor_set(v___x_1797_, 1, v_b_1772_);
                leanh::lean_ctor_set(v___x_1797_, 2, v_bkt_1790_);
                v_buckets_x27_1798_ = lean_array_uset(v_buckets_1774_, v___x_1789_, v___x_1797_);
                v___x_1799_ = leanh::lean_unsigned_to_nat(4);
                v___x_1800_ = lean_nat_mul(v_size_x27_1796_, v___x_1799_);
                v___x_1801_ = leanh::lean_unsigned_to_nat(3);
                v___x_1802_ = lean_nat_div(v___x_1800_, v___x_1801_);
                leanh::lean_dec(v___x_1800_);
                v___x_1803_ = lean_array_get_size(v_buckets_x27_1798_);
                v___x_1804_ = lean_nat_dec_le(v___x_1802_, v___x_1803_);
                leanh::lean_dec(v___x_1802_);
                if v___x_1804_ == 0 {
                    v_val_1805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(v_buckets_x27_1798_);
                    if v_isShared_1794_ == 0 {
                        leanh::lean_ctor_set(v___x_1793_, 1, v_val_1805_);
                        leanh::lean_ctor_set(v___x_1793_, 0, v_size_x27_1796_);
                        v___x_1807_ = v___x_1793_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1808_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_size_x27_1796_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_val_1805_);
                        v___x_1807_ = v_reuseFailAlloc_1808_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1794_ == 0 {
                        leanh::lean_ctor_set(v___x_1793_, 1, v_buckets_x27_1798_);
                        leanh::lean_ctor_set(v___x_1793_, 0, v_size_x27_1796_);
                        v___x_1810_ = v___x_1793_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1811_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_size_x27_1796_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_buckets_x27_1798_);
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
    mut v_m_1817_: *mut leanh::LeanObject,
    mut v_a_1818_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: u64 = 0;
    let mut v_hash_1838_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1819_ = leanh::lean_ctor_get(v_m_1817_, 1);
                v_name_1820_ = leanh::lean_ctor_get(v_a_1818_, 1);
                v___x_1821_ = lean_array_get_size(v_buckets_1819_);
                if leanh::lean_obj_tag(v_name_1820_) == 0 {
                    v___x_1837_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
                    v___y_1823_ = v___x_1837_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1838_ = leanh::lean_ctor_get_uint64(
                        v_name_1820_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_m_1839_: *mut leanh::LeanObject,
    mut v_a_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1841_: u8 = 0;
    let mut v_r_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(v_m_1839_, v_a_1840_);
    leanh::lean_dec_ref(v_a_1840_);
    leanh::lean_dec_ref(v_m_1839_);
    v_r_1842_ = leanh::lean_box((v_res_1841_) as usize);
    return v_r_1842_;
}
pub unsafe fn l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(
    mut v_self_1843_: *mut leanh::LeanObject,
    mut v_a_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toHashSet_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toArray_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1857_: u8 = 0;
    let mut v_unused_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toHashSet_1845_ = leanh::lean_ctor_get(v_self_1843_, 0);
                v_toArray_1846_ = leanh::lean_ctor_get(v_self_1843_, 1);
                v___x_1847_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(v_toHashSet_1845_, v_a_1844_);
                if v___x_1847_ == 0 {
                    leanh::lean_inc_ref(v_toArray_1846_);
                    leanh::lean_inc_ref(v_toHashSet_1845_);
                    v_isSharedCheck_1857_ = (!leanh::lean_is_exclusive(v_self_1843_)) as u8;
                    if v_isSharedCheck_1857_ == 0 {
                        v_unused_1858_ = leanh::lean_ctor_get(v_self_1843_, 1);
                        leanh::lean_dec(v_unused_1858_);
                        v_unused_1859_ = leanh::lean_ctor_get(v_self_1843_, 0);
                        leanh::lean_dec(v_unused_1859_);
                        v___x_1849_ = v_self_1843_;
                        v_isShared_1850_ = v_isSharedCheck_1857_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_self_1843_);
                        v___x_1849_ = leanh::lean_box(0);
                        v_isShared_1850_ = v_isSharedCheck_1857_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1844_);
                    return v_self_1843_;
                }
            }
            1 => {
                v___x_1851_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_a_1844_);
                v___x_1852_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(v_toHashSet_1845_, v_a_1844_, v___x_1851_);
                v___x_1853_ = lean_array_push(v_toArray_1846_, v_a_1844_);
                if v_isShared_1850_ == 0 {
                    leanh::lean_ctor_set(v___x_1849_, 1, v___x_1853_);
                    leanh::lean_ctor_set(v___x_1849_, 0, v___x_1852_);
                    v___x_1855_ = v___x_1849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1856_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1853_);
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
    mut v_as_1860_: *mut leanh::LeanObject,
    mut v_i_1861_: usize,
    mut v_stop_1862_: usize,
    mut v_b_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lib_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: usize = 0;
    let mut v___x_1869_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1864_ = lean_usize_dec_eq(v_i_1861_, v_stop_1862_);
                if v___x_1864_ == 0 {
                    v___x_1865_ = lean_array_uget_borrowed(v_as_1860_, v_i_1861_);
                    v_lib_1866_ = leanh::lean_ctor_get(v___x_1865_, 0);
                    leanh::lean_inc_ref(v_lib_1866_);
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
    mut v_as_1871_: *mut leanh::LeanObject,
    mut v_i_1872_: *mut leanh::LeanObject,
    mut v_stop_1873_: *mut leanh::LeanObject,
    mut v_b_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1875_: usize = 0;
    let mut v_stop_boxed_1876_: usize = 0;
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1875_ = leanh::lean_unbox_usize(v_i_1872_);
    leanh::lean_dec(v_i_1872_);
    v_stop_boxed_1876_ = leanh::lean_unbox_usize(v_stop_1873_);
    leanh::lean_dec(v_stop_1873_);
    v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(v_as_1871_, v_i_boxed_1875_, v_stop_boxed_1876_, v_b_1874_);
    leanh::lean_dec_ref(v_as_1871_);
    return v_res_1877_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(
    mut v___x_1878_: *mut leanh::LeanObject,
    mut v_as_1879_: *mut leanh::LeanObject,
    mut v_sz_1880_: usize,
    mut v_i_1881_: usize,
    mut v_b_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: usize = 0;
    let mut v___x_1898_: usize = 0;
    let mut v_a_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1890_ = lean_usize_dec_lt(v_i_1881_, v_sz_1880_);
                if v___x_1890_ == 0 {
                    leanh::lean_dec_ref(v___y_1883_);
                    leanh::lean_dec_ref(v___x_1878_);
                    v___x_1891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1891_, 0, v_b_1882_);
                    leanh::lean_ctor_set(v___x_1891_, 1, v___y_1888_);
                    return v___x_1891_;
                } else {
                    v_a_1892_ = lean_array_uget_borrowed(v_as_1879_, v_i_1881_);
                    leanh::lean_inc_ref(v___y_1883_);
                    leanh::lean_inc(v_a_1892_);
                    leanh::lean_inc_ref(v___x_1878_);
                    v___x_1893_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(v___x_1878_, v_a_1892_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
                    if leanh::lean_obj_tag(v___x_1893_) == 0 {
                        v_a_1894_ = leanh::lean_ctor_get(v___x_1893_, 0);
                        leanh::lean_inc(v_a_1894_);
                        v_a_1895_ = leanh::lean_ctor_get(v___x_1893_, 1);
                        leanh::lean_inc(v_a_1895_);
                        leanh::lean_dec_ref_known(v___x_1893_, 2);
                        v___x_1896_ = lean_array_push(v_b_1882_, v_a_1894_);
                        v___x_1897_ = 1usize;
                        v___x_1898_ = lean_usize_add(v_i_1881_, v___x_1897_);
                        v_i_1881_ = v___x_1898_;
                        v_b_1882_ = v___x_1896_;
                        v___y_1888_ = v_a_1895_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_1883_);
                        leanh::lean_dec_ref(v_b_1882_);
                        leanh::lean_dec_ref(v___x_1878_);
                        v_a_1900_ = leanh::lean_ctor_get(v___x_1893_, 0);
                        v_a_1901_ = leanh::lean_ctor_get(v___x_1893_, 1);
                        v_isSharedCheck_1908_ =
                            (!leanh::lean_is_exclusive(v___x_1893_)) as u8;
                        if v_isSharedCheck_1908_ == 0 {
                            v___x_1903_ = v___x_1893_;
                            v_isShared_1904_ = v_isSharedCheck_1908_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1901_);
                            leanh::lean_inc(v_a_1900_);
                            leanh::lean_dec(v___x_1893_);
                            v___x_1903_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1907_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_a_1901_);
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
    mut v___x_1909_: *mut leanh::LeanObject,
    mut v_as_1910_: *mut leanh::LeanObject,
    mut v_sz_1911_: *mut leanh::LeanObject,
    mut v_i_1912_: *mut leanh::LeanObject,
    mut v_b_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
    mut v___y_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
    mut v___y_1917_: *mut leanh::LeanObject,
    mut v___y_1918_: *mut leanh::LeanObject,
    mut v___y_1919_: *mut leanh::LeanObject,
    mut v___y_1920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1921_: usize = 0;
    let mut v_i_boxed_1922_: usize = 0;
    let mut v_res_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1921_ = leanh::lean_unbox_usize(v_sz_1911_);
    leanh::lean_dec(v_sz_1911_);
    v_i_boxed_1922_ = leanh::lean_unbox_usize(v_i_1912_);
    leanh::lean_dec(v_i_1912_);
    v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(v___x_1909_, v_as_1910_, v_sz_boxed_1921_, v_i_boxed_1922_, v_b_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
    leanh::lean_dec_ref(v___y_1918_);
    leanh::lean_dec(v___y_1917_);
    leanh::lean_dec(v___y_1916_);
    leanh::lean_dec(v___y_1915_);
    leanh::lean_dec_ref(v_as_1910_);
    return v_res_1923_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(
    mut v_a_1924_: *mut leanh::LeanObject,
    mut v_as_1925_: *mut leanh::LeanObject,
    mut v_sz_1926_: usize,
    mut v_i_1927_: usize,
    mut v_b_1928_: *mut leanh::LeanObject,
    mut v___y_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
    mut v___y_1933_: *mut leanh::LeanObject,
    mut v___y_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1936_: u8 = 0;
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: usize = 0;
    let mut v_a_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1936_ = lean_usize_dec_lt(v_i_1927_, v_sz_1926_);
                if v___x_1936_ == 0 {
                    leanh::lean_dec_ref(v___y_1929_);
                    leanh::lean_dec_ref(v_a_1924_);
                    v___x_1937_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1937_, 0, v_b_1928_);
                    leanh::lean_ctor_set(v___x_1937_, 1, v___y_1934_);
                    return v___x_1937_;
                } else {
                    v_pkg_1938_ = leanh::lean_ctor_get(v_a_1924_, 0);
                    v_a_1939_ = lean_array_uget_borrowed(v_as_1925_, v_i_1927_);
                    leanh::lean_inc_ref(v___y_1929_);
                    leanh::lean_inc(v_a_1939_);
                    leanh::lean_inc_ref(v_pkg_1938_);
                    v___x_1940_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(v_pkg_1938_, v_a_1939_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
                    if leanh::lean_obj_tag(v___x_1940_) == 0 {
                        v_a_1941_ = leanh::lean_ctor_get(v___x_1940_, 0);
                        leanh::lean_inc(v_a_1941_);
                        v_a_1942_ = leanh::lean_ctor_get(v___x_1940_, 1);
                        leanh::lean_inc(v_a_1942_);
                        leanh::lean_dec_ref_known(v___x_1940_, 2);
                        v___x_1943_ = lean_array_push(v_b_1928_, v_a_1941_);
                        v___x_1944_ = 1usize;
                        v___x_1945_ = lean_usize_add(v_i_1927_, v___x_1944_);
                        v_i_1927_ = v___x_1945_;
                        v_b_1928_ = v___x_1943_;
                        v___y_1934_ = v_a_1942_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_1929_);
                        leanh::lean_dec_ref(v_b_1928_);
                        leanh::lean_dec_ref(v_a_1924_);
                        v_a_1947_ = leanh::lean_ctor_get(v___x_1940_, 0);
                        v_a_1948_ = leanh::lean_ctor_get(v___x_1940_, 1);
                        v_isSharedCheck_1955_ =
                            (!leanh::lean_is_exclusive(v___x_1940_)) as u8;
                        if v_isSharedCheck_1955_ == 0 {
                            v___x_1950_ = v___x_1940_;
                            v_isShared_1951_ = v_isSharedCheck_1955_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1948_);
                            leanh::lean_inc(v_a_1947_);
                            leanh::lean_dec(v___x_1940_);
                            v___x_1950_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1954_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_a_1948_);
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
    mut v_a_1956_: *mut leanh::LeanObject,
    mut v_as_1957_: *mut leanh::LeanObject,
    mut v_sz_1958_: *mut leanh::LeanObject,
    mut v_i_1959_: *mut leanh::LeanObject,
    mut v_b_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
    mut v___y_1964_: *mut leanh::LeanObject,
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1968_: usize = 0;
    let mut v_i_boxed_1969_: usize = 0;
    let mut v_res_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1968_ = leanh::lean_unbox_usize(v_sz_1958_);
    leanh::lean_dec(v_sz_1958_);
    v_i_boxed_1969_ = leanh::lean_unbox_usize(v_i_1959_);
    leanh::lean_dec(v_i_1959_);
    v_res_1970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(v_a_1956_, v_as_1957_, v_sz_boxed_1968_, v_i_boxed_1969_, v_b_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
    leanh::lean_dec_ref(v___y_1965_);
    leanh::lean_dec(v___y_1964_);
    leanh::lean_dec(v___y_1963_);
    leanh::lean_dec(v___y_1962_);
    leanh::lean_dec_ref(v_as_1957_);
    return v_res_1970_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(
    mut v_a_1971_: *mut leanh::LeanObject,
    mut v_as_1972_: *mut leanh::LeanObject,
    mut v_sz_1973_: usize,
    mut v_i_1974_: usize,
    mut v_b_1975_: *mut leanh::LeanObject,
    mut v___y_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
    mut v___y_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: usize = 0;
    let mut v_a_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1983_ = lean_usize_dec_lt(v_i_1974_, v_sz_1973_);
                if v___x_1983_ == 0 {
                    leanh::lean_dec_ref(v___y_1976_);
                    leanh::lean_dec_ref(v_a_1971_);
                    v___x_1984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1984_, 0, v_b_1975_);
                    leanh::lean_ctor_set(v___x_1984_, 1, v___y_1981_);
                    return v___x_1984_;
                } else {
                    v_pkg_1985_ = leanh::lean_ctor_get(v_a_1971_, 0);
                    v_a_1986_ = lean_array_uget_borrowed(v_as_1972_, v_i_1974_);
                    leanh::lean_inc_ref(v___y_1976_);
                    leanh::lean_inc(v_a_1986_);
                    leanh::lean_inc_ref(v_pkg_1985_);
                    v___x_1987_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(v_pkg_1985_, v_a_1986_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
                    if leanh::lean_obj_tag(v___x_1987_) == 0 {
                        v_a_1988_ = leanh::lean_ctor_get(v___x_1987_, 0);
                        leanh::lean_inc(v_a_1988_);
                        v_a_1989_ = leanh::lean_ctor_get(v___x_1987_, 1);
                        leanh::lean_inc(v_a_1989_);
                        leanh::lean_dec_ref_known(v___x_1987_, 2);
                        v___x_1990_ = lean_array_push(v_b_1975_, v_a_1988_);
                        v___x_1991_ = 1usize;
                        v___x_1992_ = lean_usize_add(v_i_1974_, v___x_1991_);
                        v_i_1974_ = v___x_1992_;
                        v_b_1975_ = v___x_1990_;
                        v___y_1981_ = v_a_1989_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_1976_);
                        leanh::lean_dec_ref(v_b_1975_);
                        leanh::lean_dec_ref(v_a_1971_);
                        v_a_1994_ = leanh::lean_ctor_get(v___x_1987_, 0);
                        v_a_1995_ = leanh::lean_ctor_get(v___x_1987_, 1);
                        v_isSharedCheck_2002_ =
                            (!leanh::lean_is_exclusive(v___x_1987_)) as u8;
                        if v_isSharedCheck_2002_ == 0 {
                            v___x_1997_ = v___x_1987_;
                            v_isShared_1998_ = v_isSharedCheck_2002_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1995_);
                            leanh::lean_inc(v_a_1994_);
                            leanh::lean_dec(v___x_1987_);
                            v___x_1997_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2001_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_a_1995_);
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
    mut v_a_2003_: *mut leanh::LeanObject,
    mut v_as_2004_: *mut leanh::LeanObject,
    mut v_sz_2005_: *mut leanh::LeanObject,
    mut v_i_2006_: *mut leanh::LeanObject,
    mut v_b_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
    mut v___y_2010_: *mut leanh::LeanObject,
    mut v___y_2011_: *mut leanh::LeanObject,
    mut v___y_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2015_: usize = 0;
    let mut v_i_boxed_2016_: usize = 0;
    let mut v_res_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2015_ = leanh::lean_unbox_usize(v_sz_2005_);
    leanh::lean_dec(v_sz_2005_);
    v_i_boxed_2016_ = leanh::lean_unbox_usize(v_i_2006_);
    leanh::lean_dec(v_i_2006_);
    v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(v_a_2003_, v_as_2004_, v_sz_boxed_2015_, v_i_boxed_2016_, v_b_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
    leanh::lean_dec_ref(v___y_2012_);
    leanh::lean_dec(v___y_2011_);
    leanh::lean_dec(v___y_2010_);
    leanh::lean_dec(v___y_2009_);
    leanh::lean_dec_ref(v_as_2004_);
    return v_res_2017_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(
    mut v_as_2018_: *mut leanh::LeanObject,
    mut v_sz_2019_: usize,
    mut v_i_2020_: usize,
    mut v_b_2021_: *mut leanh::LeanObject,
    mut v___y_2022_: *mut leanh::LeanObject,
    mut v___y_2023_: *mut leanh::LeanObject,
    mut v___y_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2039_: u8 = 0;
    let mut v_a_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2051_: usize = 0;
    let mut v___x_2052_: usize = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2057_: usize = 0;
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: usize = 0;
    let mut v_reuseFailAlloc_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2033_ = lean_usize_dec_lt(v_i_2020_, v_sz_2019_);
                if v___x_2033_ == 0 {
                    leanh::lean_dec_ref(v___y_2022_);
                    v___x_2034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2034_, 0, v_b_2021_);
                    leanh::lean_ctor_set(v___x_2034_, 1, v___y_2027_);
                    return v___x_2034_;
                } else {
                    v_fst_2035_ = leanh::lean_ctor_get(v_b_2021_, 0);
                    v_snd_2036_ = leanh::lean_ctor_get(v_b_2021_, 1);
                    v_isSharedCheck_2071_ = (!leanh::lean_is_exclusive(v_b_2021_)) as u8;
                    if v_isSharedCheck_2071_ == 0 {
                        v___x_2038_ = v_b_2021_;
                        v_isShared_2039_ = v_isSharedCheck_2071_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2036_);
                        leanh::lean_inc(v_fst_2035_);
                        leanh::lean_dec(v_b_2021_);
                        v___x_2038_ = leanh::lean_box(0);
                        v_isShared_2039_ = v_isSharedCheck_2071_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2032_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2032_, 0, v_a_2030_);
                leanh::lean_ctor_set(v___x_2032_, 1, v_a_2031_);
                return v___x_2032_;
            }
            2 => {
                v_a_2040_ = lean_array_uget_borrowed(v_as_2018_, v_i_2020_);
                v_pkg_2041_ = leanh::lean_ctor_get(v_a_2040_, 0);
                v_config_2042_ = leanh::lean_ctor_get(v_pkg_2041_, 6);
                v_toLeanConfig_2043_ = leanh::lean_ctor_get(v_config_2042_, 1);
                v_config_2044_ = leanh::lean_ctor_get(v_a_2040_, 2);
                v_toLeanConfig_2045_ = leanh::lean_ctor_get(v_config_2044_, 0);
                v_moreLinkObjs_2046_ = leanh::lean_ctor_get(v_toLeanConfig_2043_, 6);
                v_moreLinkLibs_2047_ = leanh::lean_ctor_get(v_toLeanConfig_2043_, 7);
                v_moreLinkObjs_2048_ = leanh::lean_ctor_get(v_toLeanConfig_2045_, 6);
                v_moreLinkLibs_2049_ = leanh::lean_ctor_get(v_toLeanConfig_2045_, 7);
                leanh::lean_inc_ref(v_moreLinkObjs_2046_);
                v___x_2050_ = l_Array_append___redArg(v_moreLinkObjs_2046_, v_moreLinkObjs_2048_);
                v_sz_2051_ = lean_array_size(v___x_2050_);
                v___x_2052_ = 0usize;
                leanh::lean_inc_ref(v___y_2022_);
                leanh::lean_inc(v_a_2040_);
                v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(v_a_2040_, v___x_2050_, v_sz_2051_, v___x_2052_, v_fst_2035_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
                leanh::lean_dec_ref(v___x_2050_);
                if leanh::lean_obj_tag(v___x_2053_) == 0 {
                    v_a_2054_ = leanh::lean_ctor_get(v___x_2053_, 0);
                    leanh::lean_inc(v_a_2054_);
                    v_a_2055_ = leanh::lean_ctor_get(v___x_2053_, 1);
                    leanh::lean_inc(v_a_2055_);
                    leanh::lean_dec_ref_known(v___x_2053_, 2);
                    leanh::lean_inc_ref(v_moreLinkLibs_2047_);
                    v___x_2056_ =
                        l_Array_append___redArg(v_moreLinkLibs_2047_, v_moreLinkLibs_2049_);
                    v_sz_2057_ = lean_array_size(v___x_2056_);
                    leanh::lean_inc_ref(v___y_2022_);
                    leanh::lean_inc(v_a_2040_);
                    v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(v_a_2040_, v___x_2056_, v_sz_2057_, v___x_2052_, v_snd_2036_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v_a_2055_);
                    leanh::lean_dec_ref(v___x_2056_);
                    if leanh::lean_obj_tag(v___x_2058_) == 0 {
                        v_a_2059_ = leanh::lean_ctor_get(v___x_2058_, 0);
                        leanh::lean_inc(v_a_2059_);
                        v_a_2060_ = leanh::lean_ctor_get(v___x_2058_, 1);
                        leanh::lean_inc(v_a_2060_);
                        leanh::lean_dec_ref_known(v___x_2058_, 2);
                        if v_isShared_2039_ == 0 {
                            leanh::lean_ctor_set(v___x_2038_, 1, v_a_2059_);
                            leanh::lean_ctor_set(v___x_2038_, 0, v_a_2054_);
                            v___x_2062_ = v___x_2038_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2066_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2054_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_a_2059_);
                            v___x_2062_ = v_reuseFailAlloc_2066_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2054_);
                        leanh::lean_del_object(v___x_2038_);
                        leanh::lean_dec_ref(v___y_2022_);
                        v_a_2067_ = leanh::lean_ctor_get(v___x_2058_, 0);
                        leanh::lean_inc(v_a_2067_);
                        v_a_2068_ = leanh::lean_ctor_get(v___x_2058_, 1);
                        leanh::lean_inc(v_a_2068_);
                        leanh::lean_dec_ref_known(v___x_2058_, 2);
                        v_a_2030_ = v_a_2067_;
                        v_a_2031_ = v_a_2068_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2038_);
                    leanh::lean_dec(v_snd_2036_);
                    leanh::lean_dec_ref(v___y_2022_);
                    v_a_2069_ = leanh::lean_ctor_get(v___x_2053_, 0);
                    leanh::lean_inc(v_a_2069_);
                    v_a_2070_ = leanh::lean_ctor_get(v___x_2053_, 1);
                    leanh::lean_inc(v_a_2070_);
                    leanh::lean_dec_ref_known(v___x_2053_, 2);
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
    mut v_as_2072_: *mut leanh::LeanObject,
    mut v_sz_2073_: *mut leanh::LeanObject,
    mut v_i_2074_: *mut leanh::LeanObject,
    mut v_b_2075_: *mut leanh::LeanObject,
    mut v___y_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2083_: usize = 0;
    let mut v_i_boxed_2084_: usize = 0;
    let mut v_res_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2083_ = leanh::lean_unbox_usize(v_sz_2073_);
    leanh::lean_dec(v_sz_2073_);
    v_i_boxed_2084_ = leanh::lean_unbox_usize(v_i_2074_);
    leanh::lean_dec(v_i_2074_);
    v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(v_as_2072_, v_sz_boxed_2083_, v_i_boxed_2084_, v_b_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
    leanh::lean_dec_ref(v___y_2080_);
    leanh::lean_dec(v___y_2079_);
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec(v___y_2077_);
    leanh::lean_dec_ref(v_as_2072_);
    return v_res_2085_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(
    mut v___x_2086_: *mut leanh::LeanObject,
    mut v_as_2087_: *mut leanh::LeanObject,
    mut v_sz_2088_: usize,
    mut v_i_2089_: usize,
    mut v_b_2090_: *mut leanh::LeanObject,
    mut v___y_2091_: *mut leanh::LeanObject,
    mut v___y_2092_: *mut leanh::LeanObject,
    mut v___y_2093_: *mut leanh::LeanObject,
    mut v___y_2094_: *mut leanh::LeanObject,
    mut v___y_2095_: *mut leanh::LeanObject,
    mut v___y_2096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: usize = 0;
    let mut v___x_2106_: usize = 0;
    let mut v_a_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2098_ = lean_usize_dec_lt(v_i_2089_, v_sz_2088_);
                if v___x_2098_ == 0 {
                    leanh::lean_dec_ref(v___y_2091_);
                    leanh::lean_dec_ref(v___x_2086_);
                    v___x_2099_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2099_, 0, v_b_2090_);
                    leanh::lean_ctor_set(v___x_2099_, 1, v___y_2096_);
                    return v___x_2099_;
                } else {
                    v_a_2100_ = lean_array_uget_borrowed(v_as_2087_, v_i_2089_);
                    leanh::lean_inc_ref(v___y_2091_);
                    leanh::lean_inc(v_a_2100_);
                    leanh::lean_inc_ref(v___x_2086_);
                    v___x_2101_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(v___x_2086_, v_a_2100_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
                    if leanh::lean_obj_tag(v___x_2101_) == 0 {
                        v_a_2102_ = leanh::lean_ctor_get(v___x_2101_, 0);
                        leanh::lean_inc(v_a_2102_);
                        v_a_2103_ = leanh::lean_ctor_get(v___x_2101_, 1);
                        leanh::lean_inc(v_a_2103_);
                        leanh::lean_dec_ref_known(v___x_2101_, 2);
                        v___x_2104_ = lean_array_push(v_b_2090_, v_a_2102_);
                        v___x_2105_ = 1usize;
                        v___x_2106_ = lean_usize_add(v_i_2089_, v___x_2105_);
                        v_i_2089_ = v___x_2106_;
                        v_b_2090_ = v___x_2104_;
                        v___y_2096_ = v_a_2103_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_2091_);
                        leanh::lean_dec_ref(v_b_2090_);
                        leanh::lean_dec_ref(v___x_2086_);
                        v_a_2108_ = leanh::lean_ctor_get(v___x_2101_, 0);
                        v_a_2109_ = leanh::lean_ctor_get(v___x_2101_, 1);
                        v_isSharedCheck_2116_ =
                            (!leanh::lean_is_exclusive(v___x_2101_)) as u8;
                        if v_isSharedCheck_2116_ == 0 {
                            v___x_2111_ = v___x_2101_;
                            v_isShared_2112_ = v_isSharedCheck_2116_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2109_);
                            leanh::lean_inc(v_a_2108_);
                            leanh::lean_dec(v___x_2101_);
                            v___x_2111_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2115_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_a_2109_);
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
    mut v___x_2117_: *mut leanh::LeanObject,
    mut v_as_2118_: *mut leanh::LeanObject,
    mut v_sz_2119_: *mut leanh::LeanObject,
    mut v_i_2120_: *mut leanh::LeanObject,
    mut v_b_2121_: *mut leanh::LeanObject,
    mut v___y_2122_: *mut leanh::LeanObject,
    mut v___y_2123_: *mut leanh::LeanObject,
    mut v___y_2124_: *mut leanh::LeanObject,
    mut v___y_2125_: *mut leanh::LeanObject,
    mut v___y_2126_: *mut leanh::LeanObject,
    mut v___y_2127_: *mut leanh::LeanObject,
    mut v___y_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2129_: usize = 0;
    let mut v_i_boxed_2130_: usize = 0;
    let mut v_res_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2129_ = leanh::lean_unbox_usize(v_sz_2119_);
    leanh::lean_dec(v_sz_2119_);
    v_i_boxed_2130_ = leanh::lean_unbox_usize(v_i_2120_);
    leanh::lean_dec(v_i_2120_);
    v_res_2131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(v___x_2117_, v_as_2118_, v_sz_boxed_2129_, v_i_boxed_2130_, v_b_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
    leanh::lean_dec_ref(v___y_2126_);
    leanh::lean_dec(v___y_2125_);
    leanh::lean_dec(v___y_2124_);
    leanh::lean_dec(v___y_2123_);
    leanh::lean_dec_ref(v_as_2118_);
    return v_res_2131_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(
    mut v_a_2132_: *mut leanh::LeanObject,
    mut v_as_2133_: *mut leanh::LeanObject,
    mut v_sz_2134_: usize,
    mut v_i_2135_: usize,
    mut v_b_2136_: *mut leanh::LeanObject,
    mut v___y_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
    mut v___y_2140_: *mut leanh::LeanObject,
    mut v___y_2141_: *mut leanh::LeanObject,
    mut v___y_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: usize = 0;
    let mut v___x_2152_: usize = 0;
    let mut v_a_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2144_ = lean_usize_dec_lt(v_i_2135_, v_sz_2134_);
                if v___x_2144_ == 0 {
                    leanh::lean_dec_ref(v___y_2137_);
                    leanh::lean_dec_ref(v_a_2132_);
                    v___x_2145_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2145_, 0, v_b_2136_);
                    leanh::lean_ctor_set(v___x_2145_, 1, v___y_2142_);
                    return v___x_2145_;
                } else {
                    v_a_2146_ = lean_array_uget_borrowed(v_as_2133_, v_i_2135_);
                    leanh::lean_inc_ref(v___y_2137_);
                    leanh::lean_inc_ref(v_a_2132_);
                    leanh::lean_inc(v_a_2146_);
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
                    if leanh::lean_obj_tag(v___x_2147_) == 0 {
                        v_a_2148_ = leanh::lean_ctor_get(v___x_2147_, 0);
                        leanh::lean_inc(v_a_2148_);
                        v_a_2149_ = leanh::lean_ctor_get(v___x_2147_, 1);
                        leanh::lean_inc(v_a_2149_);
                        leanh::lean_dec_ref_known(v___x_2147_, 2);
                        v___x_2150_ = lean_array_push(v_b_2136_, v_a_2148_);
                        v___x_2151_ = 1usize;
                        v___x_2152_ = lean_usize_add(v_i_2135_, v___x_2151_);
                        v_i_2135_ = v___x_2152_;
                        v_b_2136_ = v___x_2150_;
                        v___y_2142_ = v_a_2149_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_2137_);
                        leanh::lean_dec_ref(v_b_2136_);
                        leanh::lean_dec_ref(v_a_2132_);
                        v_a_2154_ = leanh::lean_ctor_get(v___x_2147_, 0);
                        v_a_2155_ = leanh::lean_ctor_get(v___x_2147_, 1);
                        v_isSharedCheck_2162_ =
                            (!leanh::lean_is_exclusive(v___x_2147_)) as u8;
                        if v_isSharedCheck_2162_ == 0 {
                            v___x_2157_ = v___x_2147_;
                            v_isShared_2158_ = v_isSharedCheck_2162_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2155_);
                            leanh::lean_inc(v_a_2154_);
                            leanh::lean_dec(v___x_2147_);
                            v___x_2157_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2161_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2155_);
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
    mut v_a_2163_: *mut leanh::LeanObject,
    mut v_as_2164_: *mut leanh::LeanObject,
    mut v_sz_2165_: *mut leanh::LeanObject,
    mut v_i_2166_: *mut leanh::LeanObject,
    mut v_b_2167_: *mut leanh::LeanObject,
    mut v___y_2168_: *mut leanh::LeanObject,
    mut v___y_2169_: *mut leanh::LeanObject,
    mut v___y_2170_: *mut leanh::LeanObject,
    mut v___y_2171_: *mut leanh::LeanObject,
    mut v___y_2172_: *mut leanh::LeanObject,
    mut v___y_2173_: *mut leanh::LeanObject,
    mut v___y_2174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2175_: usize = 0;
    let mut v_i_boxed_2176_: usize = 0;
    let mut v_res_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2175_ = leanh::lean_unbox_usize(v_sz_2165_);
    leanh::lean_dec(v_sz_2165_);
    v_i_boxed_2176_ = leanh::lean_unbox_usize(v_i_2166_);
    leanh::lean_dec(v_i_2166_);
    v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(v_a_2163_, v_as_2164_, v_sz_boxed_2175_, v_i_boxed_2176_, v_b_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
    leanh::lean_dec_ref(v___y_2172_);
    leanh::lean_dec(v___y_2171_);
    leanh::lean_dec(v___y_2170_);
    leanh::lean_dec(v___y_2169_);
    leanh::lean_dec_ref(v_as_2164_);
    return v_res_2177_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(
    mut v_shouldExport_2178_: u8,
    mut v_as_2179_: *mut leanh::LeanObject,
    mut v_sz_2180_: usize,
    mut v_i_2181_: usize,
    mut v_b_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
    mut v___y_2184_: *mut leanh::LeanObject,
    mut v___y_2185_: *mut leanh::LeanObject,
    mut v___y_2186_: *mut leanh::LeanObject,
    mut v___y_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lib_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2198_: usize = 0;
    let mut v___x_2199_: usize = 0;
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2190_ = lean_usize_dec_lt(v_i_2181_, v_sz_2180_);
                if v___x_2190_ == 0 {
                    leanh::lean_dec_ref(v___y_2183_);
                    v___x_2191_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2191_, 0, v_b_2182_);
                    leanh::lean_ctor_set(v___x_2191_, 1, v___y_2188_);
                    return v___x_2191_;
                } else {
                    v_a_2192_ = lean_array_uget_borrowed(v_as_2179_, v_i_2181_);
                    v_lib_2193_ = leanh::lean_ctor_get(v_a_2192_, 0);
                    v_config_2194_ = leanh::lean_ctor_get(v_lib_2193_, 2);
                    v_nativeFacets_2195_ = leanh::lean_ctor_get(v_config_2194_, 8);
                    v___x_2196_ = leanh::lean_box((v_shouldExport_2178_) as usize);
                    leanh::lean_inc_ref(v_nativeFacets_2195_);
                    v___x_2197_ = leanh::lean_apply_1(v_nativeFacets_2195_, v___x_2196_);
                    v_sz_2198_ = lean_array_size(v___x_2197_);
                    v___x_2199_ = 0usize;
                    leanh::lean_inc_ref(v___y_2183_);
                    leanh::lean_inc(v_a_2192_);
                    v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(v_a_2192_, v___x_2197_, v_sz_2198_, v___x_2199_, v_b_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
                    leanh::lean_dec_ref(v___x_2197_);
                    if leanh::lean_obj_tag(v___x_2200_) == 0 {
                        v_a_2201_ = leanh::lean_ctor_get(v___x_2200_, 0);
                        leanh::lean_inc(v_a_2201_);
                        v_a_2202_ = leanh::lean_ctor_get(v___x_2200_, 1);
                        leanh::lean_inc(v_a_2202_);
                        leanh::lean_dec_ref_known(v___x_2200_, 2);
                        v___x_2203_ = 1usize;
                        v___x_2204_ = lean_usize_add(v_i_2181_, v___x_2203_);
                        v_i_2181_ = v___x_2204_;
                        v_b_2182_ = v_a_2201_;
                        v___y_2188_ = v_a_2202_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_2183_);
                        return v___x_2200_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8___boxed(
    mut v_shouldExport_2206_: *mut leanh::LeanObject,
    mut v_as_2207_: *mut leanh::LeanObject,
    mut v_sz_2208_: *mut leanh::LeanObject,
    mut v_i_2209_: *mut leanh::LeanObject,
    mut v_b_2210_: *mut leanh::LeanObject,
    mut v___y_2211_: *mut leanh::LeanObject,
    mut v___y_2212_: *mut leanh::LeanObject,
    mut v___y_2213_: *mut leanh::LeanObject,
    mut v___y_2214_: *mut leanh::LeanObject,
    mut v___y_2215_: *mut leanh::LeanObject,
    mut v___y_2216_: *mut leanh::LeanObject,
    mut v___y_2217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shouldExport_boxed_2218_: u8 = 0;
    let mut v_sz_boxed_2219_: usize = 0;
    let mut v_i_boxed_2220_: usize = 0;
    let mut v_res_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_2218_ = (leanh::lean_unbox(v_shouldExport_2206_) as u8);
    v_sz_boxed_2219_ = leanh::lean_unbox_usize(v_sz_2208_);
    leanh::lean_dec(v_sz_2208_);
    v_i_boxed_2220_ = leanh::lean_unbox_usize(v_i_2209_);
    leanh::lean_dec(v_i_2209_);
    v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(v_shouldExport_boxed_2218_, v_as_2207_, v_sz_boxed_2219_, v_i_boxed_2220_, v_b_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
    leanh::lean_dec_ref(v___y_2215_);
    leanh::lean_dec(v___y_2214_);
    leanh::lean_dec(v___y_2213_);
    leanh::lean_dec(v___y_2212_);
    leanh::lean_dec_ref(v_as_2207_);
    return v_res_2221_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(
    mut v_a_2222_: *mut leanh::LeanObject,
    mut v_as_2223_: *mut leanh::LeanObject,
    mut v_i_2224_: usize,
    mut v_stop_2225_: usize,
    mut v_b_2226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: usize = 0;
    let mut v___x_2230_: usize = 0;
    let mut v___x_2232_: u8 = 0;
    let mut v_toConfigDecl_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2232_ = lean_usize_dec_eq(v_i_2224_, v_stop_2225_);
                if v___x_2232_ == 0 {
                    v_toConfigDecl_2233_ = lean_array_uget_borrowed(v_as_2223_, v_i_2224_);
                    v_name_2234_ = leanh::lean_ctor_get(v_toConfigDecl_2233_, 1);
                    v_kind_2235_ = leanh::lean_ctor_get(v_toConfigDecl_2233_, 2);
                    v_config_2236_ = leanh::lean_ctor_get(v_toConfigDecl_2233_, 3);
                    v___x_2237_ = l_Lake_ExternLib_keyword;
                    v___x_2238_ = lean_name_eq(v_kind_2235_, v___x_2237_);
                    if v___x_2238_ == 0 {
                        v___y_2228_ = v_b_2226_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_config_2236_);
                        leanh::lean_inc(v_name_2234_);
                        leanh::lean_inc_ref(v_a_2222_);
                        v___x_2239_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2239_, 0, v_a_2222_);
                        leanh::lean_ctor_set(v___x_2239_, 1, v_name_2234_);
                        leanh::lean_ctor_set(v___x_2239_, 2, v_config_2236_);
                        v___x_2240_ = lean_array_push(v_b_2226_, v___x_2239_);
                        v___y_2228_ = v___x_2240_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_2222_);
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
    mut v_a_2241_: *mut leanh::LeanObject,
    mut v_as_2242_: *mut leanh::LeanObject,
    mut v_i_2243_: *mut leanh::LeanObject,
    mut v_stop_2244_: *mut leanh::LeanObject,
    mut v_b_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2246_: usize = 0;
    let mut v_stop_boxed_2247_: usize = 0;
    let mut v_res_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2246_ = leanh::lean_unbox_usize(v_i_2243_);
    leanh::lean_dec(v_i_2243_);
    v_stop_boxed_2247_ = leanh::lean_unbox_usize(v_stop_2244_);
    leanh::lean_dec(v_stop_2244_);
    v_res_2248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(v_a_2241_, v_as_2242_, v_i_boxed_2246_, v_stop_boxed_2247_, v_b_2245_);
    leanh::lean_dec_ref(v_as_2242_);
    return v_res_2248_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(
    mut v_as_2249_: *mut leanh::LeanObject,
    mut v_sz_2250_: usize,
    mut v_i_2251_: usize,
    mut v_b_2252_: *mut leanh::LeanObject,
    mut v___y_2253_: *mut leanh::LeanObject,
    mut v___y_2254_: *mut leanh::LeanObject,
    mut v___y_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
    mut v___y_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: usize = 0;
    let mut v___x_2275_: usize = 0;
    let mut v_a_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2260_ = lean_usize_dec_lt(v_i_2251_, v_sz_2250_);
                if v___x_2260_ == 0 {
                    leanh::lean_dec_ref(v___y_2253_);
                    v___x_2261_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2261_, 0, v_b_2252_);
                    leanh::lean_ctor_set(v___x_2261_, 1, v___y_2258_);
                    return v___x_2261_;
                } else {
                    v_a_2262_ = lean_array_uget_borrowed(v_as_2249_, v_i_2251_);
                    v_pkg_2263_ = leanh::lean_ctor_get(v_a_2262_, 0);
                    v_name_2264_ = leanh::lean_ctor_get(v_a_2262_, 1);
                    v_keyName_2265_ = leanh::lean_ctor_get(v_pkg_2263_, 2);
                    v___x_2266_ = l_Lake_ExternLib_staticFacet;
                    leanh::lean_inc(v_name_2264_);
                    leanh::lean_inc(v_keyName_2265_);
                    v___x_2267_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2267_, 0, v_keyName_2265_);
                    leanh::lean_ctor_set(v___x_2267_, 1, v_name_2264_);
                    v___x_2268_ = l_Lake_ExternLib_keyword;
                    leanh::lean_inc(v_a_2262_);
                    v___x_2269_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2269_, 0, v___x_2267_);
                    leanh::lean_ctor_set(v___x_2269_, 1, v___x_2268_);
                    leanh::lean_ctor_set(v___x_2269_, 2, v_a_2262_);
                    leanh::lean_ctor_set(v___x_2269_, 3, v___x_2266_);
                    leanh::lean_inc_ref(v___y_2253_);
                    leanh::lean_inc_ref(v___y_2257_);
                    leanh::lean_inc(v___y_2256_);
                    leanh::lean_inc(v___y_2255_);
                    leanh::lean_inc(v___y_2254_);
                    v___x_2270_ = leanh::lean_apply_7(
                        v___y_2253_,
                        v___x_2269_,
                        v___y_2254_,
                        v___y_2255_,
                        v___y_2256_,
                        v___y_2257_,
                        v___y_2258_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2270_) == 0 {
                        v_a_2271_ = leanh::lean_ctor_get(v___x_2270_, 0);
                        leanh::lean_inc(v_a_2271_);
                        v_a_2272_ = leanh::lean_ctor_get(v___x_2270_, 1);
                        leanh::lean_inc(v_a_2272_);
                        leanh::lean_dec_ref_known(v___x_2270_, 2);
                        v___x_2273_ = lean_array_push(v_b_2252_, v_a_2271_);
                        v___x_2274_ = 1usize;
                        v___x_2275_ = lean_usize_add(v_i_2251_, v___x_2274_);
                        v_i_2251_ = v___x_2275_;
                        v_b_2252_ = v___x_2273_;
                        v___y_2258_ = v_a_2272_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_2253_);
                        leanh::lean_dec_ref(v_b_2252_);
                        v_a_2277_ = leanh::lean_ctor_get(v___x_2270_, 0);
                        v_a_2278_ = leanh::lean_ctor_get(v___x_2270_, 1);
                        v_isSharedCheck_2285_ =
                            (!leanh::lean_is_exclusive(v___x_2270_)) as u8;
                        if v_isSharedCheck_2285_ == 0 {
                            v___x_2280_ = v___x_2270_;
                            v_isShared_2281_ = v_isSharedCheck_2285_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2278_);
                            leanh::lean_inc(v_a_2277_);
                            leanh::lean_dec(v___x_2270_);
                            v___x_2280_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2284_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2277_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_a_2278_);
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
    mut v_as_2286_: *mut leanh::LeanObject,
    mut v_sz_2287_: *mut leanh::LeanObject,
    mut v_i_2288_: *mut leanh::LeanObject,
    mut v_b_2289_: *mut leanh::LeanObject,
    mut v___y_2290_: *mut leanh::LeanObject,
    mut v___y_2291_: *mut leanh::LeanObject,
    mut v___y_2292_: *mut leanh::LeanObject,
    mut v___y_2293_: *mut leanh::LeanObject,
    mut v___y_2294_: *mut leanh::LeanObject,
    mut v___y_2295_: *mut leanh::LeanObject,
    mut v___y_2296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2297_: usize = 0;
    let mut v_i_boxed_2298_: usize = 0;
    let mut v_res_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2297_ = leanh::lean_unbox_usize(v_sz_2287_);
    leanh::lean_dec(v_sz_2287_);
    v_i_boxed_2298_ = leanh::lean_unbox_usize(v_i_2288_);
    leanh::lean_dec(v_i_2288_);
    v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v_as_2286_, v_sz_boxed_2297_, v_i_boxed_2298_, v_b_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
    leanh::lean_dec_ref(v___y_2294_);
    leanh::lean_dec(v___y_2293_);
    leanh::lean_dec(v___y_2292_);
    leanh::lean_dec(v___y_2291_);
    leanh::lean_dec_ref(v_as_2286_);
    return v_res_2299_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(
    mut v_as_2302_: *mut leanh::LeanObject,
    mut v_sz_2303_: usize,
    mut v_i_2304_: usize,
    mut v_b_2305_: *mut leanh::LeanObject,
    mut v___y_2306_: *mut leanh::LeanObject,
    mut v___y_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: usize = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: usize = 0;
    let mut v___x_2333_: usize = 0;
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: usize = 0;
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2323_ = lean_usize_dec_lt(v_i_2304_, v_sz_2303_);
                if v___x_2323_ == 0 {
                    leanh::lean_dec_ref(v___y_2306_);
                    v___x_2324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2324_, 0, v_b_2305_);
                    leanh::lean_ctor_set(v___x_2324_, 1, v___y_2311_);
                    return v___x_2324_;
                } else {
                    v_a_2325_ = lean_array_uget_borrowed(v_as_2302_, v_i_2304_);
                    v_targetDecls_2326_ = leanh::lean_ctor_get(v_a_2325_, 14);
                    v___x_2327_ = leanh::lean_unsigned_to_nat(0);
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
                                leanh::lean_inc(v_a_2325_);
                                v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(v_a_2325_, v_targetDecls_2326_, v___x_2332_, v___x_2333_, v___x_2328_);
                                v___y_2314_ = v___x_2334_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2335_ = 0usize;
                            v___x_2336_ = lean_usize_of_nat(v___x_2329_);
                            leanh::lean_inc(v_a_2325_);
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
                leanh::lean_inc_ref(v___y_2306_);
                v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(v___y_2314_, v_sz_2315_, v___x_2316_, v_b_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
                leanh::lean_dec_ref(v___y_2314_);
                if leanh::lean_obj_tag(v___x_2317_) == 0 {
                    v_a_2318_ = leanh::lean_ctor_get(v___x_2317_, 0);
                    leanh::lean_inc(v_a_2318_);
                    v_a_2319_ = leanh::lean_ctor_get(v___x_2317_, 1);
                    leanh::lean_inc(v_a_2319_);
                    leanh::lean_dec_ref_known(v___x_2317_, 2);
                    v___x_2320_ = 1usize;
                    v___x_2321_ = lean_usize_add(v_i_2304_, v___x_2320_);
                    v_i_2304_ = v___x_2321_;
                    v_b_2305_ = v_a_2318_;
                    v___y_2311_ = v_a_2319_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_2306_);
                    return v___x_2317_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___boxed(
    mut v_as_2338_: *mut leanh::LeanObject,
    mut v_sz_2339_: *mut leanh::LeanObject,
    mut v_i_2340_: *mut leanh::LeanObject,
    mut v_b_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2349_: usize = 0;
    let mut v_i_boxed_2350_: usize = 0;
    let mut v_res_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2349_ = leanh::lean_unbox_usize(v_sz_2339_);
    leanh::lean_dec(v_sz_2339_);
    v_i_boxed_2350_ = leanh::lean_unbox_usize(v_i_2340_);
    leanh::lean_dec(v_i_2340_);
    v_res_2351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(v_as_2338_, v_sz_boxed_2349_, v_i_boxed_2350_, v_b_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
    leanh::lean_dec_ref(v___y_2346_);
    leanh::lean_dec(v___y_2345_);
    leanh::lean_dec(v___y_2344_);
    leanh::lean_dec(v___y_2343_);
    leanh::lean_dec_ref(v_as_2338_);
    return v_res_2351_;
}
pub unsafe fn _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ =
        l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0;
    v___x_2354_ = l_Lake_BuildTrace_nil(v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(
    mut v___x_2357_: *mut leanh::LeanObject,
    mut v___x_2358_: *mut leanh::LeanObject,
    mut v_sz_2359_: usize,
    mut v___x_2360_: usize,
    mut v_objJobs_2361_: *mut leanh::LeanObject,
    mut v___x_2362_: *mut leanh::LeanObject,
    mut v_pkg_2363_: *mut leanh::LeanObject,
    mut v_root_2364_: *mut leanh::LeanObject,
    mut v_supportInterpreter_2365_: u8,
    mut v_toLeanConfig_2366_: *mut leanh::LeanObject,
    mut v_libJobs_2367_: *mut leanh::LeanObject,
    mut v_exeName_2368_: *mut leanh::LeanObject,
    mut v_self_2369_: *mut leanh::LeanObject,
    mut v___x_2370_: *mut leanh::LeanObject,
    mut v___y_2371_: *mut leanh::LeanObject,
    mut v___y_2372_: *mut leanh::LeanObject,
    mut v___y_2373_: *mut leanh::LeanObject,
    mut v___y_2374_: *mut leanh::LeanObject,
    mut v___y_2375_: *mut leanh::LeanObject,
    mut v___y_2376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2393_: u8 = 0;
    let mut v_task_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2397_: usize = 0;
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2404_: usize = 0;
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toArray_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2416_: usize = 0;
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2422_: usize = 0;
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2437_: usize = 0;
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v_buildDir_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2464_: u8 = 0;
    let mut v_a_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v_a_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2482_: u8 = 0;
    let mut v_a_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_a_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2496_: u8 = 0;
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v_a_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut v_reuseFailAlloc_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2511_: u8 = 0;
    let mut v_unused_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: u8 = 0;
    let mut v___x_2516_: u8 = 0;
    let mut v___x_2517_: usize = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_a_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u8 = 0;
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2552_: u8 = 0;
    let mut v_a_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2557_: u8 = 0;
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut v_a_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v___y_2371_);
                leanh::lean_inc_ref(v___x_2357_);
                v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(v___x_2357_, v___x_2358_, v_sz_2359_, v___x_2360_, v_objJobs_2361_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
                if leanh::lean_obj_tag(v___x_2378_) == 0 {
                    v_a_2379_ = leanh::lean_ctor_get(v___x_2378_, 0);
                    leanh::lean_inc(v_a_2379_);
                    v_a_2380_ = leanh::lean_ctor_get(v___x_2378_, 1);
                    leanh::lean_inc(v_a_2380_);
                    leanh::lean_dec_ref_known(v___x_2378_, 2);
                    v_keyName_2381_ = leanh::lean_ctor_get(v_pkg_2363_, 2);
                    v_dir_2382_ = leanh::lean_ctor_get(v_pkg_2363_, 4);
                    leanh::lean_inc_ref(v_dir_2382_);
                    v_config_2383_ = leanh::lean_ctor_get(v_pkg_2363_, 6);
                    leanh::lean_inc_ref(v_config_2383_);
                    v___x_2384_ = l_Lake_Module_transImportsFacet;
                    leanh::lean_inc(v_root_2364_);
                    leanh::lean_inc(v_keyName_2381_);
                    v___x_2385_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2385_, 0, v_keyName_2381_);
                    leanh::lean_ctor_set(v___x_2385_, 1, v_root_2364_);
                    v___x_2386_ = l_Lake_Module_keyword;
                    v___x_2387_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2387_, 0, v___x_2385_);
                    leanh::lean_ctor_set(v___x_2387_, 1, v___x_2386_);
                    leanh::lean_ctor_set(v___x_2387_, 2, v___x_2357_);
                    leanh::lean_ctor_set(v___x_2387_, 3, v___x_2384_);
                    leanh::lean_inc_ref(v___y_2371_);
                    leanh::lean_inc_ref(v___y_2375_);
                    leanh::lean_inc(v___y_2374_);
                    leanh::lean_inc(v___y_2373_);
                    leanh::lean_inc(v___x_2362_);
                    v___x_2388_ = leanh::lean_apply_7(
                        v___y_2371_,
                        v___x_2387_,
                        v___x_2362_,
                        v___y_2373_,
                        v___y_2374_,
                        v___y_2375_,
                        v_a_2380_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2388_) == 0 {
                        v_a_2389_ = leanh::lean_ctor_get(v___x_2388_, 0);
                        v_a_2390_ = leanh::lean_ctor_get(v___x_2388_, 1);
                        v_isSharedCheck_2552_ =
                            (!leanh::lean_is_exclusive(v___x_2388_)) as u8;
                        if v_isSharedCheck_2552_ == 0 {
                            v___x_2392_ = v___x_2388_;
                            v_isShared_2393_ = v_isSharedCheck_2552_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2390_);
                            leanh::lean_inc(v_a_2389_);
                            leanh::lean_dec(v___x_2388_);
                            v___x_2392_ = leanh::lean_box(0);
                            v_isShared_2393_ = v_isSharedCheck_2552_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_config_2383_);
                        leanh::lean_dec_ref(v_dir_2382_);
                        leanh::lean_dec(v_a_2379_);
                        leanh::lean_dec_ref(v___y_2371_);
                        leanh::lean_dec_ref(v_self_2369_);
                        leanh::lean_dec_ref(v_exeName_2368_);
                        leanh::lean_dec_ref(v_libJobs_2367_);
                        leanh::lean_dec(v_root_2364_);
                        leanh::lean_dec_ref(v_pkg_2363_);
                        leanh::lean_dec(v___x_2362_);
                        v_a_2553_ = leanh::lean_ctor_get(v___x_2388_, 0);
                        v_a_2554_ = leanh::lean_ctor_get(v___x_2388_, 1);
                        v_isSharedCheck_2561_ =
                            (!leanh::lean_is_exclusive(v___x_2388_)) as u8;
                        if v_isSharedCheck_2561_ == 0 {
                            v___x_2556_ = v___x_2388_;
                            v_isShared_2557_ = v_isSharedCheck_2561_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2554_);
                            leanh::lean_inc(v_a_2553_);
                            leanh::lean_dec(v___x_2388_);
                            v___x_2556_ = leanh::lean_box(0);
                            v_isShared_2557_ = v_isSharedCheck_2561_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2371_);
                    leanh::lean_dec_ref(v_self_2369_);
                    leanh::lean_dec_ref(v_exeName_2368_);
                    leanh::lean_dec_ref(v_libJobs_2367_);
                    leanh::lean_dec(v_root_2364_);
                    leanh::lean_dec_ref(v_pkg_2363_);
                    leanh::lean_dec(v___x_2362_);
                    leanh::lean_dec_ref(v___x_2357_);
                    v_a_2562_ = leanh::lean_ctor_get(v___x_2378_, 0);
                    v_a_2563_ = leanh::lean_ctor_get(v___x_2378_, 1);
                    v_isSharedCheck_2570_ = (!leanh::lean_is_exclusive(v___x_2378_)) as u8;
                    if v_isSharedCheck_2570_ == 0 {
                        v___x_2565_ = v___x_2378_;
                        v_isShared_2566_ = v_isSharedCheck_2570_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2563_);
                        leanh::lean_inc(v_a_2562_);
                        leanh::lean_dec(v___x_2378_);
                        v___x_2565_ = leanh::lean_box(0);
                        v_isShared_2566_ = v_isSharedCheck_2570_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v_task_2394_ = leanh::lean_ctor_get(v_a_2389_, 0);
                leanh::lean_inc_ref(v_task_2394_);
                leanh::lean_dec(v_a_2389_);
                v___x_2395_ = lean_io_wait(v_task_2394_);
                if leanh::lean_obj_tag(v___x_2395_) == 0 {
                    leanh::lean_del_object(v___x_2392_);
                    leanh::lean_dec(v_root_2364_);
                    v_a_2396_ = leanh::lean_ctor_get(v___x_2395_, 0);
                    leanh::lean_inc(v_a_2396_);
                    leanh::lean_dec_ref_known(v___x_2395_, 2);
                    v_sz_2397_ = lean_array_size(v_a_2396_);
                    leanh::lean_inc_ref(v___y_2371_);
                    v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(v_supportInterpreter_2365_, v_a_2396_, v_sz_2397_, v___x_2360_, v_a_2379_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2390_);
                    if leanh::lean_obj_tag(v___x_2398_) == 0 {
                        v_a_2399_ = leanh::lean_ctor_get(v___x_2398_, 0);
                        leanh::lean_inc(v_a_2399_);
                        v_a_2400_ = leanh::lean_ctor_get(v___x_2398_, 1);
                        leanh::lean_inc(v_a_2400_);
                        leanh::lean_dec_ref_known(v___x_2398_, 2);
                        v_moreLinkObjs_2401_ = leanh::lean_ctor_get(v_toLeanConfig_2366_, 6);
                        v_moreLinkLibs_2402_ = leanh::lean_ctor_get(v_toLeanConfig_2366_, 7);
                        v_weakLinkArgs_2403_ = leanh::lean_ctor_get(v_toLeanConfig_2366_, 9);
                        v_sz_2404_ = lean_array_size(v_moreLinkObjs_2401_);
                        leanh::lean_inc_ref(v___y_2371_);
                        leanh::lean_inc_ref(v_pkg_2363_);
                        v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(v_pkg_2363_, v_moreLinkObjs_2401_, v_sz_2404_, v___x_2360_, v_a_2399_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2400_);
                        if leanh::lean_obj_tag(v___x_2405_) == 0 {
                            v_a_2406_ = leanh::lean_ctor_get(v___x_2405_, 0);
                            leanh::lean_inc(v_a_2406_);
                            v_a_2407_ = leanh::lean_ctor_get(v___x_2405_, 1);
                            leanh::lean_inc(v_a_2407_);
                            leanh::lean_dec_ref_known(v___x_2405_, 2);
                            v___x_2513_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13;
                            v___x_2514_ = lean_array_get_size(v_a_2396_);
                            v___x_2515_ = lean_nat_dec_lt(v___x_2370_, v___x_2514_);
                            if v___x_2515_ == 0 {
                                leanh::lean_dec(v_a_2396_);
                                v___y_2409_ = v___x_2513_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2516_ = lean_nat_dec_le(v___x_2514_, v___x_2514_);
                                if v___x_2516_ == 0 {
                                    if v___x_2515_ == 0 {
                                        leanh::lean_dec(v_a_2396_);
                                        v___y_2409_ = v___x_2513_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_2517_ = lean_usize_of_nat(v___x_2514_);
                                        v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(v_a_2396_, v___x_2360_, v___x_2517_, v___x_2513_);
                                        leanh::lean_dec(v_a_2396_);
                                        v___y_2409_ = v___x_2518_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___x_2519_ = lean_usize_of_nat(v___x_2514_);
                                    v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(v_a_2396_, v___x_2360_, v___x_2519_, v___x_2513_);
                                    leanh::lean_dec(v_a_2396_);
                                    v___y_2409_ = v___x_2520_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2396_);
                            leanh::lean_dec_ref(v_config_2383_);
                            leanh::lean_dec_ref(v_dir_2382_);
                            leanh::lean_dec_ref(v___y_2371_);
                            leanh::lean_dec_ref(v_self_2369_);
                            leanh::lean_dec_ref(v_exeName_2368_);
                            leanh::lean_dec_ref(v_libJobs_2367_);
                            leanh::lean_dec_ref(v_pkg_2363_);
                            leanh::lean_dec(v___x_2362_);
                            v_a_2521_ = leanh::lean_ctor_get(v___x_2405_, 0);
                            v_a_2522_ = leanh::lean_ctor_get(v___x_2405_, 1);
                            v_isSharedCheck_2529_ =
                                (!leanh::lean_is_exclusive(v___x_2405_)) as u8;
                            if v_isSharedCheck_2529_ == 0 {
                                v___x_2524_ = v___x_2405_;
                                v_isShared_2525_ = v_isSharedCheck_2529_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2522_);
                                leanh::lean_inc(v_a_2521_);
                                leanh::lean_dec(v___x_2405_);
                                v___x_2524_ = leanh::lean_box(0);
                                v_isShared_2525_ = v_isSharedCheck_2529_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2396_);
                        leanh::lean_dec_ref(v_config_2383_);
                        leanh::lean_dec_ref(v_dir_2382_);
                        leanh::lean_dec_ref(v___y_2371_);
                        leanh::lean_dec_ref(v_self_2369_);
                        leanh::lean_dec_ref(v_exeName_2368_);
                        leanh::lean_dec_ref(v_libJobs_2367_);
                        leanh::lean_dec_ref(v_pkg_2363_);
                        leanh::lean_dec(v___x_2362_);
                        v_a_2530_ = leanh::lean_ctor_get(v___x_2398_, 0);
                        v_a_2531_ = leanh::lean_ctor_get(v___x_2398_, 1);
                        v_isSharedCheck_2538_ =
                            (!leanh::lean_is_exclusive(v___x_2398_)) as u8;
                        if v_isSharedCheck_2538_ == 0 {
                            v___x_2533_ = v___x_2398_;
                            v_isShared_2534_ = v_isSharedCheck_2538_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2531_);
                            leanh::lean_inc(v_a_2530_);
                            leanh::lean_dec(v___x_2398_);
                            v___x_2533_ = leanh::lean_box(0);
                            v_isShared_2534_ = v_isSharedCheck_2538_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2395_);
                    leanh::lean_dec_ref(v_config_2383_);
                    leanh::lean_dec_ref(v_dir_2382_);
                    leanh::lean_dec(v_a_2379_);
                    leanh::lean_dec_ref(v___y_2371_);
                    leanh::lean_dec_ref(v_self_2369_);
                    leanh::lean_dec_ref(v_exeName_2368_);
                    leanh::lean_dec_ref(v_libJobs_2367_);
                    leanh::lean_dec_ref(v_pkg_2363_);
                    leanh::lean_dec(v___x_2362_);
                    v___x_2539_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2;
                    v___x_2540_ = 1;
                    v___x_2541_ = l_Lean_Name_toString(v_root_2364_, v___x_2540_);
                    v___x_2542_ = lean_string_append(v___x_2539_, v___x_2541_);
                    leanh::lean_dec_ref(v___x_2541_);
                    v___x_2543_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3;
                    v___x_2544_ = lean_string_append(v___x_2542_, v___x_2543_);
                    v___x_2545_ = 3;
                    v___x_2546_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_2546_, 0, v___x_2544_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2546_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_2545_,
                    );
                    v___x_2547_ = lean_array_get_size(v_a_2390_);
                    v___x_2548_ = lean_array_push(v_a_2390_, v___x_2546_);
                    if v_isShared_2393_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2392_, 1);
                        leanh::lean_ctor_set(v___x_2392_, 1, v___x_2548_);
                        leanh::lean_ctor_set(v___x_2392_, 0, v___x_2547_);
                        v___x_2550_ = v___x_2392_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2551_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2547_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___x_2548_);
                        v___x_2550_ = v_reuseFailAlloc_2551_;
                        state = 21;
                        continue;
                    }
                }
            }
            2 => {
                v_toArray_2410_ = leanh::lean_ctor_get(v___y_2409_, 1);
                v_isSharedCheck_2511_ = (!leanh::lean_is_exclusive(v___y_2409_)) as u8;
                if v_isSharedCheck_2511_ == 0 {
                    v_unused_2512_ = leanh::lean_ctor_get(v___y_2409_, 0);
                    leanh::lean_dec(v_unused_2512_);
                    v___x_2412_ = v___y_2409_;
                    v_isShared_2413_ = v_isSharedCheck_2511_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_toArray_2410_);
                    leanh::lean_dec(v___y_2409_);
                    v___x_2412_ = leanh::lean_box(0);
                    v_isShared_2413_ = v_isSharedCheck_2511_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2413_ == 0 {
                    leanh::lean_ctor_set(v___x_2412_, 1, v_libJobs_2367_);
                    leanh::lean_ctor_set(v___x_2412_, 0, v_a_2406_);
                    v___x_2415_ = v___x_2412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2510_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2406_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_libJobs_2367_);
                    v___x_2415_ = v_reuseFailAlloc_2510_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_2416_ = lean_array_size(v_toArray_2410_);
                leanh::lean_inc_ref(v___y_2371_);
                v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(v_toArray_2410_, v_sz_2416_, v___x_2360_, v___x_2415_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2407_);
                leanh::lean_dec_ref(v_toArray_2410_);
                if leanh::lean_obj_tag(v___x_2417_) == 0 {
                    v_a_2418_ = leanh::lean_ctor_get(v___x_2417_, 0);
                    leanh::lean_inc(v_a_2418_);
                    v_a_2419_ = leanh::lean_ctor_get(v___x_2417_, 1);
                    leanh::lean_inc(v_a_2419_);
                    leanh::lean_dec_ref_known(v___x_2417_, 2);
                    v_fst_2420_ = leanh::lean_ctor_get(v_a_2418_, 0);
                    leanh::lean_inc(v_fst_2420_);
                    v_snd_2421_ = leanh::lean_ctor_get(v_a_2418_, 1);
                    leanh::lean_inc(v_snd_2421_);
                    leanh::lean_dec(v_a_2418_);
                    v_sz_2422_ = lean_array_size(v_moreLinkLibs_2402_);
                    leanh::lean_inc_ref(v___y_2371_);
                    leanh::lean_inc_ref(v_pkg_2363_);
                    v___x_2423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(v_pkg_2363_, v_moreLinkLibs_2402_, v_sz_2422_, v___x_2360_, v_snd_2421_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2419_);
                    if leanh::lean_obj_tag(v___x_2423_) == 0 {
                        v_a_2424_ = leanh::lean_ctor_get(v___x_2423_, 0);
                        leanh::lean_inc(v_a_2424_);
                        v_a_2425_ = leanh::lean_ctor_get(v___x_2423_, 1);
                        leanh::lean_inc(v_a_2425_);
                        leanh::lean_dec_ref_known(v___x_2423_, 2);
                        v___x_2426_ = l_Lake_Package_transDepsFacet;
                        leanh::lean_inc(v_keyName_2381_);
                        v___x_2427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2427_, 0, v_keyName_2381_);
                        v___x_2428_ = l_Lake_Package_keyword;
                        leanh::lean_inc_ref(v_pkg_2363_);
                        v___x_2429_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_2429_, 0, v___x_2427_);
                        leanh::lean_ctor_set(v___x_2429_, 1, v___x_2428_);
                        leanh::lean_ctor_set(v___x_2429_, 2, v_pkg_2363_);
                        leanh::lean_ctor_set(v___x_2429_, 3, v___x_2426_);
                        leanh::lean_inc_ref(v___y_2371_);
                        leanh::lean_inc_ref(v___y_2375_);
                        leanh::lean_inc(v___y_2374_);
                        leanh::lean_inc(v___y_2373_);
                        leanh::lean_inc(v___x_2362_);
                        v___x_2430_ = leanh::lean_apply_7(
                            v___y_2371_,
                            v___x_2429_,
                            v___x_2362_,
                            v___y_2373_,
                            v___y_2374_,
                            v___y_2375_,
                            v_a_2425_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_2430_) == 0 {
                            v_a_2431_ = leanh::lean_ctor_get(v___x_2430_, 0);
                            leanh::lean_inc(v_a_2431_);
                            v_a_2432_ = leanh::lean_ctor_get(v___x_2430_, 1);
                            leanh::lean_inc(v_a_2432_);
                            leanh::lean_dec_ref_known(v___x_2430_, 2);
                            v___x_2433_ = l_Lake_Job_await___redArg(v_a_2431_, v_a_2432_);
                            if leanh::lean_obj_tag(v___x_2433_) == 0 {
                                v_a_2434_ = leanh::lean_ctor_get(v___x_2433_, 0);
                                leanh::lean_inc(v_a_2434_);
                                v_a_2435_ = leanh::lean_ctor_get(v___x_2433_, 1);
                                leanh::lean_inc(v_a_2435_);
                                leanh::lean_dec_ref_known(v___x_2433_, 2);
                                v___x_2436_ = lean_array_push(v_a_2434_, v_pkg_2363_);
                                v_sz_2437_ = lean_array_size(v___x_2436_);
                                leanh::lean_inc_ref(v___y_2371_);
                                v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(v___x_2436_, v_sz_2437_, v___x_2360_, v_fst_2420_, v___y_2371_, v___x_2362_, v___y_2373_, v___y_2374_, v___y_2375_, v_a_2435_);
                                leanh::lean_dec_ref(v___x_2436_);
                                if leanh::lean_obj_tag(v___x_2438_) == 0 {
                                    v_toLeanConfig_2439_ =
                                        leanh::lean_ctor_get(v_config_2383_, 1);
                                    leanh::lean_inc_ref(v_toLeanConfig_2439_);
                                    v_a_2440_ = leanh::lean_ctor_get(v___x_2438_, 0);
                                    v_a_2441_ = leanh::lean_ctor_get(v___x_2438_, 1);
                                    v_isSharedCheck_2464_ =
                                        (!leanh::lean_is_exclusive(v___x_2438_)) as u8;
                                    if v_isSharedCheck_2464_ == 0 {
                                        v___x_2443_ = v___x_2438_;
                                        v_isShared_2444_ = v_isSharedCheck_2464_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2441_);
                                        leanh::lean_inc(v_a_2440_);
                                        leanh::lean_dec(v___x_2438_);
                                        v___x_2443_ = leanh::lean_box(0);
                                        v_isShared_2444_ = v_isSharedCheck_2464_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_2424_);
                                    leanh::lean_dec_ref(v_config_2383_);
                                    leanh::lean_dec_ref(v_dir_2382_);
                                    leanh::lean_dec_ref(v___y_2371_);
                                    leanh::lean_dec_ref(v_self_2369_);
                                    leanh::lean_dec_ref(v_exeName_2368_);
                                    leanh::lean_dec(v___x_2362_);
                                    v_a_2465_ = leanh::lean_ctor_get(v___x_2438_, 0);
                                    v_a_2466_ = leanh::lean_ctor_get(v___x_2438_, 1);
                                    v_isSharedCheck_2473_ =
                                        (!leanh::lean_is_exclusive(v___x_2438_)) as u8;
                                    if v_isSharedCheck_2473_ == 0 {
                                        v___x_2468_ = v___x_2438_;
                                        v_isShared_2469_ = v_isSharedCheck_2473_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2466_);
                                        leanh::lean_inc(v_a_2465_);
                                        leanh::lean_dec(v___x_2438_);
                                        v___x_2468_ = leanh::lean_box(0);
                                        v_isShared_2469_ = v_isSharedCheck_2473_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_2424_);
                                leanh::lean_dec(v_fst_2420_);
                                leanh::lean_dec_ref(v_config_2383_);
                                leanh::lean_dec_ref(v_dir_2382_);
                                leanh::lean_dec_ref(v___y_2371_);
                                leanh::lean_dec_ref(v_self_2369_);
                                leanh::lean_dec_ref(v_exeName_2368_);
                                leanh::lean_dec_ref(v_pkg_2363_);
                                leanh::lean_dec(v___x_2362_);
                                v_a_2474_ = leanh::lean_ctor_get(v___x_2433_, 0);
                                v_a_2475_ = leanh::lean_ctor_get(v___x_2433_, 1);
                                v_isSharedCheck_2482_ =
                                    (!leanh::lean_is_exclusive(v___x_2433_)) as u8;
                                if v_isSharedCheck_2482_ == 0 {
                                    v___x_2477_ = v___x_2433_;
                                    v_isShared_2478_ = v_isSharedCheck_2482_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2475_);
                                    leanh::lean_inc(v_a_2474_);
                                    leanh::lean_dec(v___x_2433_);
                                    v___x_2477_ = leanh::lean_box(0);
                                    v_isShared_2478_ = v_isSharedCheck_2482_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2424_);
                            leanh::lean_dec(v_fst_2420_);
                            leanh::lean_dec_ref(v_config_2383_);
                            leanh::lean_dec_ref(v_dir_2382_);
                            leanh::lean_dec_ref(v___y_2371_);
                            leanh::lean_dec_ref(v_self_2369_);
                            leanh::lean_dec_ref(v_exeName_2368_);
                            leanh::lean_dec_ref(v_pkg_2363_);
                            leanh::lean_dec(v___x_2362_);
                            v_a_2483_ = leanh::lean_ctor_get(v___x_2430_, 0);
                            v_a_2484_ = leanh::lean_ctor_get(v___x_2430_, 1);
                            v_isSharedCheck_2491_ =
                                (!leanh::lean_is_exclusive(v___x_2430_)) as u8;
                            if v_isSharedCheck_2491_ == 0 {
                                v___x_2486_ = v___x_2430_;
                                v_isShared_2487_ = v_isSharedCheck_2491_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2484_);
                                leanh::lean_inc(v_a_2483_);
                                leanh::lean_dec(v___x_2430_);
                                v___x_2486_ = leanh::lean_box(0);
                                v_isShared_2487_ = v_isSharedCheck_2491_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fst_2420_);
                        leanh::lean_dec_ref(v_config_2383_);
                        leanh::lean_dec_ref(v_dir_2382_);
                        leanh::lean_dec_ref(v___y_2371_);
                        leanh::lean_dec_ref(v_self_2369_);
                        leanh::lean_dec_ref(v_exeName_2368_);
                        leanh::lean_dec_ref(v_pkg_2363_);
                        leanh::lean_dec(v___x_2362_);
                        v_a_2492_ = leanh::lean_ctor_get(v___x_2423_, 0);
                        v_a_2493_ = leanh::lean_ctor_get(v___x_2423_, 1);
                        v_isSharedCheck_2500_ =
                            (!leanh::lean_is_exclusive(v___x_2423_)) as u8;
                        if v_isSharedCheck_2500_ == 0 {
                            v___x_2495_ = v___x_2423_;
                            v_isShared_2496_ = v_isSharedCheck_2500_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2493_);
                            leanh::lean_inc(v_a_2492_);
                            leanh::lean_dec(v___x_2423_);
                            v___x_2495_ = leanh::lean_box(0);
                            v_isShared_2496_ = v_isSharedCheck_2500_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_config_2383_);
                    leanh::lean_dec_ref(v_dir_2382_);
                    leanh::lean_dec_ref(v___y_2371_);
                    leanh::lean_dec_ref(v_self_2369_);
                    leanh::lean_dec_ref(v_exeName_2368_);
                    leanh::lean_dec_ref(v_pkg_2363_);
                    leanh::lean_dec(v___x_2362_);
                    v_a_2501_ = leanh::lean_ctor_get(v___x_2417_, 0);
                    v_a_2502_ = leanh::lean_ctor_get(v___x_2417_, 1);
                    v_isSharedCheck_2509_ = (!leanh::lean_is_exclusive(v___x_2417_)) as u8;
                    if v_isSharedCheck_2509_ == 0 {
                        v___x_2504_ = v___x_2417_;
                        v_isShared_2505_ = v_isSharedCheck_2509_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2502_);
                        leanh::lean_inc(v_a_2501_);
                        leanh::lean_dec(v___x_2417_);
                        v___x_2504_ = leanh::lean_box(0);
                        v_isShared_2505_ = v_isSharedCheck_2509_;
                        state = 15;
                        continue;
                    }
                }
            }
            5 => {
                v_buildDir_2445_ = leanh::lean_ctor_get(v_config_2383_, 5);
                leanh::lean_inc_ref(v_buildDir_2445_);
                v_binDir_2446_ = leanh::lean_ctor_get(v_config_2383_, 8);
                leanh::lean_inc_ref(v_binDir_2446_);
                leanh::lean_dec_ref(v_config_2383_);
                v_weakLinkArgs_2447_ = leanh::lean_ctor_get(v_toLeanConfig_2439_, 9);
                leanh::lean_inc_ref(v_weakLinkArgs_2447_);
                leanh::lean_dec_ref(v_toLeanConfig_2439_);
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
                v___x_2459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1_once), _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1);
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
                leanh::lean_dec(v___x_2362_);
                leanh::lean_dec(v_a_2440_);
                if v_isShared_2444_ == 0 {
                    leanh::lean_ctor_set(v___x_2443_, 0, v___x_2460_);
                    v___x_2462_ = v___x_2443_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2463_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_a_2441_);
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
                    v_reuseFailAlloc_2472_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_a_2466_);
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
                    v_reuseFailAlloc_2481_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_a_2475_);
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
                    v_reuseFailAlloc_2490_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_a_2484_);
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
                    v_reuseFailAlloc_2499_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_a_2493_);
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
                    v_reuseFailAlloc_2508_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_a_2502_);
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
                    v_reuseFailAlloc_2528_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_a_2522_);
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
                    v_reuseFailAlloc_2537_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_a_2531_);
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
                    v_reuseFailAlloc_2560_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_a_2554_);
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
                    v_reuseFailAlloc_2569_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_a_2563_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2571_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_2572_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_2573_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_2574_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_objJobs_2575_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2576_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_pkg_2577_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_root_2578_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_supportInterpreter_2579_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_toLeanConfig_2580_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_libJobs_2581_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_exeName_2582_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_self_2583_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_2584_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_2585_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_2586_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_2587_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_2588_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_2589_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_2590_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_2591_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_sz_boxed_2592_: usize = 0;
    let mut v___x_108882__boxed_2593_: usize = 0;
    let mut v_supportInterpreter_boxed_2594_: u8 = 0;
    let mut v_res_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2592_ = leanh::lean_unbox_usize(v_sz_2573_);
    leanh::lean_dec(v_sz_2573_);
    v___x_108882__boxed_2593_ = leanh::lean_unbox_usize(v___x_2574_);
    leanh::lean_dec(v___x_2574_);
    v_supportInterpreter_boxed_2594_ = (leanh::lean_unbox(v_supportInterpreter_2579_) as u8);
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
    leanh::lean_dec_ref(v___y_2589_);
    leanh::lean_dec(v___y_2588_);
    leanh::lean_dec(v___y_2587_);
    leanh::lean_dec(v___y_2586_);
    leanh::lean_dec(v___x_2584_);
    leanh::lean_dec_ref(v_toLeanConfig_2580_);
    leanh::lean_dec_ref(v___x_2572_);
    return v_res_2595_;
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(
    mut v_self_2601_: *mut leanh::LeanObject,
    mut v_a_2602_: *mut leanh::LeanObject,
    mut v_a_2603_: *mut leanh::LeanObject,
    mut v_a_2604_: *mut leanh::LeanObject,
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_a_2606_: *mut leanh::LeanObject,
    mut v_a_2607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_2615_: u8 = 0;
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_objJobs_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2625_: usize = 0;
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2636_: u8 = 0;
    let mut v_task_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v_registeredJobs_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u8 = 0;
    let mut v_job_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_unused_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_2609_ = leanh::lean_ctor_get(v_self_2601_, 2);
                v_pkg_2610_ = leanh::lean_ctor_get(v_self_2601_, 0);
                leanh::lean_inc_ref_n(v_pkg_2610_, 3);
                v_name_2611_ = leanh::lean_ctor_get(v_self_2601_, 1);
                leanh::lean_inc_n(v_name_2611_, 2);
                v_toLeanConfig_2612_ = leanh::lean_ctor_get(v_config_2609_, 0);
                leanh::lean_inc_ref(v_toLeanConfig_2612_);
                v_root_2613_ = leanh::lean_ctor_get(v_config_2609_, 2);
                leanh::lean_inc_n(v_root_2613_, 2);
                v_exeName_2614_ = leanh::lean_ctor_get(v_config_2609_, 3);
                leanh::lean_inc_ref(v_exeName_2614_);
                v_supportInterpreter_2615_ = leanh::lean_ctor_get_uint8(
                    v_config_2609_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v___x_2616_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_2609_);
                v_nativeFacets_2617_ = leanh::lean_ctor_get(v___x_2616_, 8);
                leanh::lean_inc_ref(v_nativeFacets_2617_);
                v___x_2618_ = l_Lake_instDataKindFilePath;
                v___x_2619_ = leanh::lean_unsigned_to_nat(0);
                v_objJobs_2620_ =
                    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0;
                v___x_2621_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2621_, 0, v_pkg_2610_);
                leanh::lean_ctor_set(v___x_2621_, 1, v_name_2611_);
                leanh::lean_ctor_set(v___x_2621_, 2, v___x_2616_);
                v___x_2622_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2622_, 0, v___x_2621_);
                leanh::lean_ctor_set(v___x_2622_, 1, v_root_2613_);
                v___x_2623_ = leanh::lean_box((v_supportInterpreter_2615_) as usize);
                v___x_2624_ = leanh::lean_apply_1(v_nativeFacets_2617_, v___x_2623_);
                v_sz_2625_ = lean_array_size(v___x_2624_);
                v___x_2626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2626_, 0, v_pkg_2610_);
                v___x_2627_ = leanh::lean_box_usize(v_sz_2625_);
                v___x_2628_ =
                    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1;
                v___x_2629_ = leanh::lean_box((v_supportInterpreter_2615_) as usize);
                v___f_2630_ = leanh::lean_alloc_closure(
                    l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed
                        as *mut core::ffi::c_void,
                    21,
                    14,
                );
                leanh::lean_closure_set(v___f_2630_, 0, v___x_2622_);
                leanh::lean_closure_set(v___f_2630_, 1, v___x_2624_);
                leanh::lean_closure_set(v___f_2630_, 2, v___x_2627_);
                leanh::lean_closure_set(v___f_2630_, 3, v___x_2628_);
                leanh::lean_closure_set(v___f_2630_, 4, v_objJobs_2620_);
                leanh::lean_closure_set(v___f_2630_, 5, v___x_2626_);
                leanh::lean_closure_set(v___f_2630_, 6, v_pkg_2610_);
                leanh::lean_closure_set(v___f_2630_, 7, v_root_2613_);
                leanh::lean_closure_set(v___f_2630_, 8, v___x_2629_);
                leanh::lean_closure_set(v___f_2630_, 9, v_toLeanConfig_2612_);
                leanh::lean_closure_set(v___f_2630_, 10, v_objJobs_2620_);
                leanh::lean_closure_set(v___f_2630_, 11, v_exeName_2614_);
                leanh::lean_closure_set(v___f_2630_, 12, v_self_2601_);
                leanh::lean_closure_set(v___f_2630_, 13, v___x_2619_);
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
                if leanh::lean_obj_tag(v___x_2631_) == 0 {
                    v_a_2632_ = leanh::lean_ctor_get(v___x_2631_, 0);
                    v_a_2633_ = leanh::lean_ctor_get(v___x_2631_, 1);
                    v_isSharedCheck_2661_ = (!leanh::lean_is_exclusive(v___x_2631_)) as u8;
                    if v_isSharedCheck_2661_ == 0 {
                        v___x_2635_ = v___x_2631_;
                        v_isShared_2636_ = v_isSharedCheck_2661_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2633_);
                        leanh::lean_inc(v_a_2632_);
                        leanh::lean_dec(v___x_2631_);
                        v___x_2635_ = leanh::lean_box(0);
                        v_isShared_2636_ = v_isSharedCheck_2661_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_2611_);
                    return v___x_2631_;
                }
            }
            1 => {
                v_task_2637_ = leanh::lean_ctor_get(v_a_2632_, 0);
                v_kind_2638_ = leanh::lean_ctor_get(v_a_2632_, 1);
                v_isSharedCheck_2659_ = (!leanh::lean_is_exclusive(v_a_2632_)) as u8;
                if v_isSharedCheck_2659_ == 0 {
                    v_unused_2660_ = leanh::lean_ctor_get(v_a_2632_, 2);
                    leanh::lean_dec(v_unused_2660_);
                    v___x_2640_ = v_a_2632_;
                    v_isShared_2641_ = v_isSharedCheck_2659_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_kind_2638_);
                    leanh::lean_inc(v_task_2637_);
                    leanh::lean_dec(v_a_2632_);
                    v___x_2640_ = leanh::lean_box(0);
                    v_isShared_2641_ = v_isSharedCheck_2659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_2642_ = leanh::lean_ctor_get(v_a_2606_, 3);
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
                    leanh::lean_ctor_set(v___x_2640_, 2, v___x_2647_);
                    v_job_2650_ = v___x_2640_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_task_2637_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_kind_2638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 2, v___x_2647_);
                    v_job_2650_ = v_reuseFailAlloc_2658_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v_job_2650_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2648_,
                );
                leanh::lean_inc_ref(v_job_2650_);
                v___x_2651_ = l_Lake_Job_toOpaque___redArg(v_job_2650_);
                v___x_2652_ = lean_array_push(v___x_2643_, v___x_2651_);
                v___x_2653_ = lean_st_ref_set(v_registeredJobs_2642_, v___x_2652_);
                v___x_2654_ = l_Lake_Job_renew___redArg(v_job_2650_);
                if v_isShared_2636_ == 0 {
                    leanh::lean_ctor_set(v___x_2635_, 0, v___x_2654_);
                    v___x_2656_ = v___x_2635_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_a_2633_);
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
    mut v_self_2662_: *mut leanh::LeanObject,
    mut v_a_2663_: *mut leanh::LeanObject,
    mut v_a_2664_: *mut leanh::LeanObject,
    mut v_a_2665_: *mut leanh::LeanObject,
    mut v_a_2666_: *mut leanh::LeanObject,
    mut v_a_2667_: *mut leanh::LeanObject,
    mut v_a_2668_: *mut leanh::LeanObject,
    mut v_a_2669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2670_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(
        v_self_2662_,
        v_a_2663_,
        v_a_2664_,
        v_a_2665_,
        v_a_2666_,
        v_a_2667_,
        v_a_2668_,
    );
    leanh::lean_dec_ref(v_a_2667_);
    leanh::lean_dec(v_a_2666_);
    leanh::lean_dec(v_a_2665_);
    leanh::lean_dec(v_a_2664_);
    return v_res_2670_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(
    mut v_00_u03b2_2671_: *mut leanh::LeanObject,
    mut v_m_2672_: *mut leanh::LeanObject,
    mut v_a_2673_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2674_: u8 = 0;
    v___x_2674_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(v_m_2672_, v_a_2673_);
    return v___x_2674_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___boxed(
    mut v_00_u03b2_2675_: *mut leanh::LeanObject,
    mut v_m_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2678_: u8 = 0;
    let mut v_r_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(v_00_u03b2_2675_, v_m_2676_, v_a_2677_);
    leanh::lean_dec_ref(v_a_2677_);
    leanh::lean_dec_ref(v_m_2676_);
    v_r_2679_ = leanh::lean_box((v_res_2678_) as usize);
    return v_r_2679_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1(
    mut v_00_u03b2_2680_: *mut leanh::LeanObject,
    mut v_m_2681_: *mut leanh::LeanObject,
    mut v_a_2682_: *mut leanh::LeanObject,
    mut v_b_2683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2684_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(v_m_2681_, v_a_2682_, v_b_2683_);
    return v___x_2684_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4(
    mut v_00_u03b2_2685_: *mut leanh::LeanObject,
    mut v_a_2686_: *mut leanh::LeanObject,
    mut v_x_2687_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2688_: u8 = 0;
    v___x_2688_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(v_a_2686_, v_x_2687_);
    return v___x_2688_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b2_2689_: *mut leanh::LeanObject,
    mut v_a_2690_: *mut leanh::LeanObject,
    mut v_x_2691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2692_: u8 = 0;
    let mut v_r_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2692_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4(v_00_u03b2_2689_, v_a_2690_, v_x_2691_);
    leanh::lean_dec(v_x_2691_);
    leanh::lean_dec_ref(v_a_2690_);
    v_r_2693_ = leanh::lean_box((v_res_2692_) as usize);
    return v_r_2693_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6(
    mut v_00_u03b2_2694_: *mut leanh::LeanObject,
    mut v_data_2695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(v_data_2695_);
    return v___x_2696_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18(
    mut v_00_u03b2_2697_: *mut leanh::LeanObject,
    mut v_i_2698_: *mut leanh::LeanObject,
    mut v_source_2699_: *mut leanh::LeanObject,
    mut v_target_2700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2701_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(v_i_2698_, v_source_2699_, v_target_2700_);
    return v___x_2701_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19(
    mut v_00_u03b2_2702_: *mut leanh::LeanObject,
    mut v_x_2703_: *mut leanh::LeanObject,
    mut v_x_2704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(v_x_2703_, v_x_2704_);
    return v___x_2705_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(
    mut v_fmt_2706_: u8,
    mut v_a_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_fmt_2706_ == 0 {
        return v_a_2707_;
    } else {
        let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2708_ = l_Lake_mkRelPathString(v_a_2707_);
        v___x_2709_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2709_, 0, v___x_2708_);
        v___x_2710_ = l_Lean_Json_compress(v___x_2709_);
        return v___x_2710_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(
    mut v_fmt_2711_: *mut leanh::LeanObject,
    mut v_a_2712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fmt_boxed_2713_: u8 = 0;
    let mut v_res_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fmt_boxed_2713_ = (leanh::lean_unbox(v_fmt_2711_) as u8);
    v_res_2714_ = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(
        v_fmt_boxed_2713_,
        v_a_2712_,
    );
    return v_res_2714_;
}
pub unsafe fn _init_l_Lake_LeanExe_exeFacetConfig___closed__2() -> *mut leanh::LeanObject {
    let mut v___f_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: u8 = 0;
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2717_ = l_Lake_LeanExe_exeFacetConfig___closed__0;
    v___x_2718_ = 1;
    v___x_2719_ = l_Lake_instDataKindFilePath;
    v___x_2720_ = l_Lake_LeanExe_exeFacetConfig___closed__1;
    v___x_2721_ = l_Lake_LeanExe_keyword;
    v___x_2722_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
    leanh::lean_ctor_set(v___x_2722_, 0, v___x_2721_);
    leanh::lean_ctor_set(v___x_2722_, 1, v___x_2720_);
    leanh::lean_ctor_set(v___x_2722_, 2, v___x_2719_);
    leanh::lean_ctor_set(v___x_2722_, 3, v___f_2717_);
    leanh::lean_ctor_set_uint8(
        v___x_2722_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_2718_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2722_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
        v___x_2718_,
    );
    return v___x_2722_;
}
pub unsafe fn _init_l_Lake_LeanExe_exeFacetConfig() -> *mut leanh::LeanObject {
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExe_exeFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_LeanExe_exeFacetConfig___closed__2_once),
        _init_l_Lake_LeanExe_exeFacetConfig___closed__2,
    );
    return v___x_2723_;
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(
    mut v_lib_2724_: *mut leanh::LeanObject,
    mut v_a_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
    mut v_a_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_2732_ = leanh::lean_ctor_get(v_lib_2724_, 0);
    v_name_2733_ = leanh::lean_ctor_get(v_lib_2724_, 1);
    v_keyName_2734_ = leanh::lean_ctor_get(v_pkg_2732_, 2);
    v___x_2735_ = l_Lake_LeanExe_exeFacet;
    leanh::lean_inc(v_name_2733_);
    leanh::lean_inc(v_keyName_2734_);
    v___x_2736_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2736_, 0, v_keyName_2734_);
    leanh::lean_ctor_set(v___x_2736_, 1, v_name_2733_);
    v___x_2737_ = l_Lake_LeanExe_keyword;
    v___x_2738_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2738_, 0, v___x_2736_);
    leanh::lean_ctor_set(v___x_2738_, 1, v___x_2737_);
    leanh::lean_ctor_set(v___x_2738_, 2, v_lib_2724_);
    leanh::lean_ctor_set(v___x_2738_, 3, v___x_2735_);
    leanh::lean_inc_ref(v_a_2729_);
    leanh::lean_inc(v_a_2728_);
    leanh::lean_inc(v_a_2727_);
    leanh::lean_inc(v_a_2726_);
    v___x_2739_ = leanh::lean_apply_7(
        v_a_2725_,
        v___x_2738_,
        v_a_2726_,
        v_a_2727_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        leanh::lean_box(0),
    );
    return v___x_2739_;
}
pub unsafe fn l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(
    mut v_lib_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_a_2744_: *mut leanh::LeanObject,
    mut v_a_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2748_ = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(
        v_lib_2740_,
        v_a_2741_,
        v_a_2742_,
        v_a_2743_,
        v_a_2744_,
        v_a_2745_,
        v_a_2746_,
    );
    leanh::lean_dec_ref(v_a_2745_);
    leanh::lean_dec(v_a_2744_);
    leanh::lean_dec(v_a_2743_);
    leanh::lean_dec(v_a_2742_);
    return v_res_2748_;
}
pub unsafe fn _init_l_Lake_LeanExe_defaultFacetConfig___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_2750_: u8 = 0;
    let mut v___f_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2750_ = 0;
    v___f_2751_ = l_Lake_LeanExe_exeFacetConfig___closed__0;
    v___x_2752_ = 1;
    v___x_2753_ = l_Lake_instDataKindFilePath;
    v___x_2754_ = l_Lake_LeanExe_defaultFacetConfig___closed__0;
    v___x_2755_ = l_Lake_LeanExe_keyword;
    v___x_2756_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
    leanh::lean_ctor_set(v___x_2756_, 0, v___x_2755_);
    leanh::lean_ctor_set(v___x_2756_, 1, v___x_2754_);
    leanh::lean_ctor_set(v___x_2756_, 2, v___x_2753_);
    leanh::lean_ctor_set(v___x_2756_, 3, v___f_2751_);
    leanh::lean_ctor_set_uint8(
        v___x_2756_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_2752_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2756_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
        v___x_2750_,
    );
    return v___x_2756_;
}
pub unsafe fn _init_l_Lake_LeanExe_defaultFacetConfig() -> *mut leanh::LeanObject {
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2757_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExe_defaultFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanExe_defaultFacetConfig___closed__1_once),
        _init_l_Lake_LeanExe_defaultFacetConfig___closed__1,
    );
    return v___x_2757_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(
    mut v_k_2758_: *mut leanh::LeanObject,
    mut v_v_2759_: *mut leanh::LeanObject,
    mut v_t_2760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2768_: u8 = 0;
    let mut v___x_2769_: u8 = 0;
    let mut v_impl_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v_size_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2800_: u8 = 0;
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut v_unused_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_unused_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_unused_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v_unused_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2879_: u8 = 0;
    let mut v_k_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v_unused_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut v_unused_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v_size_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: u8 = 0;
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2965_: u8 = 0;
    let mut v_unused_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2982_: u8 = 0;
    let mut v_unused_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_unused_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v_k_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut v_unused_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut v_unused_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2760_) == 0 {
                    v_size_2761_ = leanh::lean_ctor_get(v_t_2760_, 0);
                    v_k_2762_ = leanh::lean_ctor_get(v_t_2760_, 1);
                    v_v_2763_ = leanh::lean_ctor_get(v_t_2760_, 2);
                    v_l_2764_ = leanh::lean_ctor_get(v_t_2760_, 3);
                    v_r_2765_ = leanh::lean_ctor_get(v_t_2760_, 4);
                    v_isSharedCheck_3045_ = (!leanh::lean_is_exclusive(v_t_2760_)) as u8;
                    if v_isSharedCheck_3045_ == 0 {
                        v___x_2767_ = v_t_2760_;
                        v_isShared_2768_ = v_isSharedCheck_3045_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_2765_);
                        leanh::lean_inc(v_l_2764_);
                        leanh::lean_inc(v_v_2763_);
                        leanh::lean_inc(v_k_2762_);
                        leanh::lean_inc(v_size_2761_);
                        leanh::lean_dec(v_t_2760_);
                        v___x_2767_ = leanh::lean_box(0);
                        v_isShared_2768_ = v_isSharedCheck_3045_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3046_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3047_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_3047_, 0, v___x_3046_);
                    leanh::lean_ctor_set(v___x_3047_, 1, v_k_2758_);
                    leanh::lean_ctor_set(v___x_3047_, 2, v_v_2759_);
                    leanh::lean_ctor_set(v___x_3047_, 3, v_t_2760_);
                    leanh::lean_ctor_set(v___x_3047_, 4, v_t_2760_);
                    return v___x_3047_;
                }
            }
            1 => {
                v___x_2769_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2758_, v_k_2762_);
                match v___x_2769_ {
                    0 => {
                        leanh::lean_dec(v_size_2761_);
                        v_impl_2770_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_2758_, v_v_2759_, v_l_2764_);
                        v___x_2771_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_2765_) == 0 {
                            v_size_2772_ = leanh::lean_ctor_get(v_r_2765_, 0);
                            v_size_2773_ = leanh::lean_ctor_get(v_impl_2770_, 0);
                            leanh::lean_inc(v_size_2773_);
                            v_k_2774_ = leanh::lean_ctor_get(v_impl_2770_, 1);
                            leanh::lean_inc(v_k_2774_);
                            v_v_2775_ = leanh::lean_ctor_get(v_impl_2770_, 2);
                            leanh::lean_inc(v_v_2775_);
                            v_l_2776_ = leanh::lean_ctor_get(v_impl_2770_, 3);
                            leanh::lean_inc(v_l_2776_);
                            v_r_2777_ = leanh::lean_ctor_get(v_impl_2770_, 4);
                            leanh::lean_inc(v_r_2777_);
                            v___x_2778_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2779_ = lean_nat_mul(v___x_2778_, v_size_2772_);
                            v___x_2780_ = lean_nat_dec_lt(v___x_2779_, v_size_2773_);
                            leanh::lean_dec(v___x_2779_);
                            if v___x_2780_ == 0 {
                                leanh::lean_dec(v_r_2777_);
                                leanh::lean_dec(v_l_2776_);
                                leanh::lean_dec(v_v_2775_);
                                leanh::lean_dec(v_k_2774_);
                                v___x_2781_ = lean_nat_add(v___x_2771_, v_size_2773_);
                                leanh::lean_dec(v_size_2773_);
                                v___x_2782_ = lean_nat_add(v___x_2781_, v_size_2772_);
                                leanh::lean_dec(v___x_2781_);
                                if v_isShared_2768_ == 0 {
                                    leanh::lean_ctor_set(v___x_2767_, 3, v_impl_2770_);
                                    leanh::lean_ctor_set(v___x_2767_, 0, v___x_2782_);
                                    v___x_2784_ = v___x_2767_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2785_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        0,
                                        v___x_2782_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        1,
                                        v_k_2762_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        2,
                                        v_v_2763_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2785_,
                                        3,
                                        v_impl_2770_,
                                    );
                                    leanh::lean_ctor_set(
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
                                    (!leanh::lean_is_exclusive(v_impl_2770_)) as u8;
                                if v_isSharedCheck_2851_ == 0 {
                                    v_unused_2852_ = leanh::lean_ctor_get(v_impl_2770_, 4);
                                    leanh::lean_dec(v_unused_2852_);
                                    v_unused_2853_ = leanh::lean_ctor_get(v_impl_2770_, 3);
                                    leanh::lean_dec(v_unused_2853_);
                                    v_unused_2854_ = leanh::lean_ctor_get(v_impl_2770_, 2);
                                    leanh::lean_dec(v_unused_2854_);
                                    v_unused_2855_ = leanh::lean_ctor_get(v_impl_2770_, 1);
                                    leanh::lean_dec(v_unused_2855_);
                                    v_unused_2856_ = leanh::lean_ctor_get(v_impl_2770_, 0);
                                    leanh::lean_dec(v_unused_2856_);
                                    v___x_2787_ = v_impl_2770_;
                                    v_isShared_2788_ = v_isSharedCheck_2851_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_2770_);
                                    v___x_2787_ = leanh::lean_box(0);
                                    v_isShared_2788_ = v_isSharedCheck_2851_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2857_ = leanh::lean_ctor_get(v_impl_2770_, 3);
                            leanh::lean_inc(v_l_2857_);
                            if leanh::lean_obj_tag(v_l_2857_) == 0 {
                                v_r_2858_ = leanh::lean_ctor_get(v_impl_2770_, 4);
                                v_k_2859_ = leanh::lean_ctor_get(v_impl_2770_, 1);
                                v_v_2860_ = leanh::lean_ctor_get(v_impl_2770_, 2);
                                v_isSharedCheck_2871_ =
                                    (!leanh::lean_is_exclusive(v_impl_2770_)) as u8;
                                if v_isSharedCheck_2871_ == 0 {
                                    v_unused_2872_ = leanh::lean_ctor_get(v_impl_2770_, 3);
                                    leanh::lean_dec(v_unused_2872_);
                                    v_unused_2873_ = leanh::lean_ctor_get(v_impl_2770_, 0);
                                    leanh::lean_dec(v_unused_2873_);
                                    v___x_2862_ = v_impl_2770_;
                                    v_isShared_2863_ = v_isSharedCheck_2871_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_2858_);
                                    leanh::lean_inc(v_v_2860_);
                                    leanh::lean_inc(v_k_2859_);
                                    leanh::lean_dec(v_impl_2770_);
                                    v___x_2862_ = leanh::lean_box(0);
                                    v_isShared_2863_ = v_isSharedCheck_2871_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2874_ = leanh::lean_ctor_get(v_impl_2770_, 4);
                                leanh::lean_inc(v_r_2874_);
                                if leanh::lean_obj_tag(v_r_2874_) == 0 {
                                    v_k_2875_ = leanh::lean_ctor_get(v_impl_2770_, 1);
                                    v_v_2876_ = leanh::lean_ctor_get(v_impl_2770_, 2);
                                    v_isSharedCheck_2899_ =
                                        (!leanh::lean_is_exclusive(v_impl_2770_)) as u8;
                                    if v_isSharedCheck_2899_ == 0 {
                                        v_unused_2900_ =
                                            leanh::lean_ctor_get(v_impl_2770_, 4);
                                        leanh::lean_dec(v_unused_2900_);
                                        v_unused_2901_ =
                                            leanh::lean_ctor_get(v_impl_2770_, 3);
                                        leanh::lean_dec(v_unused_2901_);
                                        v_unused_2902_ =
                                            leanh::lean_ctor_get(v_impl_2770_, 0);
                                        leanh::lean_dec(v_unused_2902_);
                                        v___x_2878_ = v_impl_2770_;
                                        v_isShared_2879_ = v_isSharedCheck_2899_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2876_);
                                        leanh::lean_inc(v_k_2875_);
                                        leanh::lean_dec(v_impl_2770_);
                                        v___x_2878_ = leanh::lean_box(0);
                                        v_isShared_2879_ = v_isSharedCheck_2899_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_2903_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2768_ == 0 {
                                        leanh::lean_ctor_set(v___x_2767_, 4, v_r_2874_);
                                        leanh::lean_ctor_set(v___x_2767_, 3, v_impl_2770_);
                                        leanh::lean_ctor_set(v___x_2767_, 0, v___x_2903_);
                                        v___x_2905_ = v___x_2767_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2906_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            0,
                                            v___x_2903_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            1,
                                            v_k_2762_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            2,
                                            v_v_2763_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2906_,
                                            3,
                                            v_impl_2770_,
                                        );
                                        leanh::lean_ctor_set(
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
                        leanh::lean_dec(v_v_2763_);
                        leanh::lean_dec(v_k_2762_);
                        if v_isShared_2768_ == 0 {
                            leanh::lean_ctor_set(v___x_2767_, 2, v_v_2759_);
                            leanh::lean_ctor_set(v___x_2767_, 1, v_k_2758_);
                            v___x_2908_ = v___x_2767_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2909_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_size_2761_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_k_2758_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_v_2759_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 3, v_l_2764_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 4, v_r_2765_);
                            v___x_2908_ = v_reuseFailAlloc_2909_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_2761_);
                        v_impl_2910_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(v_k_2758_, v_v_2759_, v_r_2765_);
                        v___x_2911_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_2764_) == 0 {
                            v_size_2912_ = leanh::lean_ctor_get(v_l_2764_, 0);
                            v_size_2913_ = leanh::lean_ctor_get(v_impl_2910_, 0);
                            leanh::lean_inc(v_size_2913_);
                            v_k_2914_ = leanh::lean_ctor_get(v_impl_2910_, 1);
                            leanh::lean_inc(v_k_2914_);
                            v_v_2915_ = leanh::lean_ctor_get(v_impl_2910_, 2);
                            leanh::lean_inc(v_v_2915_);
                            v_l_2916_ = leanh::lean_ctor_get(v_impl_2910_, 3);
                            leanh::lean_inc(v_l_2916_);
                            v_r_2917_ = leanh::lean_ctor_get(v_impl_2910_, 4);
                            leanh::lean_inc(v_r_2917_);
                            v___x_2918_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2919_ = lean_nat_mul(v___x_2918_, v_size_2912_);
                            v___x_2920_ = lean_nat_dec_lt(v___x_2919_, v_size_2913_);
                            leanh::lean_dec(v___x_2919_);
                            if v___x_2920_ == 0 {
                                leanh::lean_dec(v_r_2917_);
                                leanh::lean_dec(v_l_2916_);
                                leanh::lean_dec(v_v_2915_);
                                leanh::lean_dec(v_k_2914_);
                                v___x_2921_ = lean_nat_add(v___x_2911_, v_size_2912_);
                                v___x_2922_ = lean_nat_add(v___x_2921_, v_size_2913_);
                                leanh::lean_dec(v_size_2913_);
                                leanh::lean_dec(v___x_2921_);
                                if v_isShared_2768_ == 0 {
                                    leanh::lean_ctor_set(v___x_2767_, 4, v_impl_2910_);
                                    leanh::lean_ctor_set(v___x_2767_, 0, v___x_2922_);
                                    v___x_2924_ = v___x_2767_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2925_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        0,
                                        v___x_2922_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        1,
                                        v_k_2762_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        2,
                                        v_v_2763_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2925_,
                                        3,
                                        v_l_2764_,
                                    );
                                    leanh::lean_ctor_set(
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
                                    (!leanh::lean_is_exclusive(v_impl_2910_)) as u8;
                                if v_isSharedCheck_2989_ == 0 {
                                    v_unused_2990_ = leanh::lean_ctor_get(v_impl_2910_, 4);
                                    leanh::lean_dec(v_unused_2990_);
                                    v_unused_2991_ = leanh::lean_ctor_get(v_impl_2910_, 3);
                                    leanh::lean_dec(v_unused_2991_);
                                    v_unused_2992_ = leanh::lean_ctor_get(v_impl_2910_, 2);
                                    leanh::lean_dec(v_unused_2992_);
                                    v_unused_2993_ = leanh::lean_ctor_get(v_impl_2910_, 1);
                                    leanh::lean_dec(v_unused_2993_);
                                    v_unused_2994_ = leanh::lean_ctor_get(v_impl_2910_, 0);
                                    leanh::lean_dec(v_unused_2994_);
                                    v___x_2927_ = v_impl_2910_;
                                    v_isShared_2928_ = v_isSharedCheck_2989_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_2910_);
                                    v___x_2927_ = leanh::lean_box(0);
                                    v_isShared_2928_ = v_isSharedCheck_2989_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2995_ = leanh::lean_ctor_get(v_impl_2910_, 3);
                            leanh::lean_inc(v_l_2995_);
                            if leanh::lean_obj_tag(v_l_2995_) == 0 {
                                v_r_2996_ = leanh::lean_ctor_get(v_impl_2910_, 4);
                                v_k_2997_ = leanh::lean_ctor_get(v_impl_2910_, 1);
                                v_v_2998_ = leanh::lean_ctor_get(v_impl_2910_, 2);
                                v_isSharedCheck_3021_ =
                                    (!leanh::lean_is_exclusive(v_impl_2910_)) as u8;
                                if v_isSharedCheck_3021_ == 0 {
                                    v_unused_3022_ = leanh::lean_ctor_get(v_impl_2910_, 3);
                                    leanh::lean_dec(v_unused_3022_);
                                    v_unused_3023_ = leanh::lean_ctor_get(v_impl_2910_, 0);
                                    leanh::lean_dec(v_unused_3023_);
                                    v___x_3000_ = v_impl_2910_;
                                    v_isShared_3001_ = v_isSharedCheck_3021_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_2996_);
                                    leanh::lean_inc(v_v_2998_);
                                    leanh::lean_inc(v_k_2997_);
                                    leanh::lean_dec(v_impl_2910_);
                                    v___x_3000_ = leanh::lean_box(0);
                                    v_isShared_3001_ = v_isSharedCheck_3021_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3024_ = leanh::lean_ctor_get(v_impl_2910_, 4);
                                leanh::lean_inc(v_r_3024_);
                                if leanh::lean_obj_tag(v_r_3024_) == 0 {
                                    v_k_3025_ = leanh::lean_ctor_get(v_impl_2910_, 1);
                                    v_v_3026_ = leanh::lean_ctor_get(v_impl_2910_, 2);
                                    v_isSharedCheck_3037_ =
                                        (!leanh::lean_is_exclusive(v_impl_2910_)) as u8;
                                    if v_isSharedCheck_3037_ == 0 {
                                        v_unused_3038_ =
                                            leanh::lean_ctor_get(v_impl_2910_, 4);
                                        leanh::lean_dec(v_unused_3038_);
                                        v_unused_3039_ =
                                            leanh::lean_ctor_get(v_impl_2910_, 3);
                                        leanh::lean_dec(v_unused_3039_);
                                        v_unused_3040_ =
                                            leanh::lean_ctor_get(v_impl_2910_, 0);
                                        leanh::lean_dec(v_unused_3040_);
                                        v___x_3028_ = v_impl_2910_;
                                        v_isShared_3029_ = v_isSharedCheck_3037_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_3026_);
                                        leanh::lean_inc(v_k_3025_);
                                        leanh::lean_dec(v_impl_2910_);
                                        v___x_3028_ = leanh::lean_box(0);
                                        v_isShared_3029_ = v_isSharedCheck_3037_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3041_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2768_ == 0 {
                                        leanh::lean_ctor_set(v___x_2767_, 4, v_impl_2910_);
                                        leanh::lean_ctor_set(v___x_2767_, 3, v_r_3024_);
                                        leanh::lean_ctor_set(v___x_2767_, 0, v___x_3041_);
                                        v___x_3043_ = v___x_2767_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3044_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            0,
                                            v___x_3041_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            1,
                                            v_k_2762_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            2,
                                            v_v_2763_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3044_,
                                            3,
                                            v_r_3024_,
                                        );
                                        leanh::lean_ctor_set(
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
                v_size_2789_ = leanh::lean_ctor_get(v_l_2776_, 0);
                v_size_2790_ = leanh::lean_ctor_get(v_r_2777_, 0);
                v_k_2791_ = leanh::lean_ctor_get(v_r_2777_, 1);
                v_v_2792_ = leanh::lean_ctor_get(v_r_2777_, 2);
                v_l_2793_ = leanh::lean_ctor_get(v_r_2777_, 3);
                v_r_2794_ = leanh::lean_ctor_get(v_r_2777_, 4);
                v___x_2795_ = leanh::lean_unsigned_to_nat(2);
                v___x_2796_ = lean_nat_mul(v___x_2795_, v_size_2789_);
                v___x_2797_ = lean_nat_dec_lt(v_size_2790_, v___x_2796_);
                leanh::lean_dec(v___x_2796_);
                if v___x_2797_ == 0 {
                    leanh::lean_inc(v_r_2794_);
                    leanh::lean_inc(v_l_2793_);
                    leanh::lean_inc(v_v_2792_);
                    leanh::lean_inc(v_k_2791_);
                    v_isSharedCheck_2826_ = (!leanh::lean_is_exclusive(v_r_2777_)) as u8;
                    if v_isSharedCheck_2826_ == 0 {
                        v_unused_2827_ = leanh::lean_ctor_get(v_r_2777_, 4);
                        leanh::lean_dec(v_unused_2827_);
                        v_unused_2828_ = leanh::lean_ctor_get(v_r_2777_, 3);
                        leanh::lean_dec(v_unused_2828_);
                        v_unused_2829_ = leanh::lean_ctor_get(v_r_2777_, 2);
                        leanh::lean_dec(v_unused_2829_);
                        v_unused_2830_ = leanh::lean_ctor_get(v_r_2777_, 1);
                        leanh::lean_dec(v_unused_2830_);
                        v_unused_2831_ = leanh::lean_ctor_get(v_r_2777_, 0);
                        leanh::lean_dec(v_unused_2831_);
                        v___x_2799_ = v_r_2777_;
                        v_isShared_2800_ = v_isSharedCheck_2826_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_2777_);
                        v___x_2799_ = leanh::lean_box(0);
                        v_isShared_2800_ = v_isSharedCheck_2826_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2767_);
                    v___x_2832_ = lean_nat_add(v___x_2771_, v_size_2773_);
                    leanh::lean_dec(v_size_2773_);
                    v___x_2833_ = lean_nat_add(v___x_2832_, v_size_2772_);
                    leanh::lean_dec(v___x_2832_);
                    v___x_2834_ = lean_nat_add(v___x_2771_, v_size_2772_);
                    v___x_2835_ = lean_nat_add(v___x_2834_, v_size_2790_);
                    leanh::lean_dec(v___x_2834_);
                    leanh::lean_inc_ref(v_r_2765_);
                    if v_isShared_2788_ == 0 {
                        leanh::lean_ctor_set(v___x_2787_, 4, v_r_2765_);
                        leanh::lean_ctor_set(v___x_2787_, 3, v_r_2777_);
                        leanh::lean_ctor_set(v___x_2787_, 2, v_v_2763_);
                        leanh::lean_ctor_set(v___x_2787_, 1, v_k_2762_);
                        leanh::lean_ctor_set(v___x_2787_, 0, v___x_2835_);
                        v___x_2837_ = v___x_2787_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2850_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2835_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_k_2762_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_v_2763_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_r_2777_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_r_2765_);
                        v___x_2837_ = v_reuseFailAlloc_2850_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2801_ = lean_nat_add(v___x_2771_, v_size_2773_);
                leanh::lean_dec(v_size_2773_);
                v___x_2802_ = lean_nat_add(v___x_2801_, v_size_2772_);
                leanh::lean_dec(v___x_2801_);
                v___x_2814_ = lean_nat_add(v___x_2771_, v_size_2789_);
                if leanh::lean_obj_tag(v_l_2793_) == 0 {
                    v_size_2824_ = leanh::lean_ctor_get(v_l_2793_, 0);
                    leanh::lean_inc(v_size_2824_);
                    v___y_2816_ = v_size_2824_;
                    state = 8;
                    continue;
                } else {
                    v___x_2825_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2816_ = v___x_2825_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2807_ = lean_nat_add(v___y_2805_, v___y_2806_);
                leanh::lean_dec(v___y_2806_);
                leanh::lean_dec(v___y_2805_);
                if v_isShared_2800_ == 0 {
                    leanh::lean_ctor_set(v___x_2799_, 4, v_r_2765_);
                    leanh::lean_ctor_set(v___x_2799_, 3, v_r_2794_);
                    leanh::lean_ctor_set(v___x_2799_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v___x_2799_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v___x_2799_, 0, v___x_2807_);
                    v___x_2809_ = v___x_2799_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2807_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_r_2794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_r_2765_);
                    v___x_2809_ = v_reuseFailAlloc_2813_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2788_ == 0 {
                    leanh::lean_ctor_set(v___x_2787_, 4, v___x_2809_);
                    leanh::lean_ctor_set(v___x_2787_, 3, v___y_2804_);
                    leanh::lean_ctor_set(v___x_2787_, 2, v_v_2792_);
                    leanh::lean_ctor_set(v___x_2787_, 1, v_k_2791_);
                    leanh::lean_ctor_set(v___x_2787_, 0, v___x_2802_);
                    v___x_2811_ = v___x_2787_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2812_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_k_2791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_v_2792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 3, v___y_2804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2812_, 4, v___x_2809_);
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
                leanh::lean_dec(v___y_2816_);
                leanh::lean_dec(v___x_2814_);
                if v_isShared_2768_ == 0 {
                    leanh::lean_ctor_set(v___x_2767_, 4, v_l_2793_);
                    leanh::lean_ctor_set(v___x_2767_, 3, v_l_2776_);
                    leanh::lean_ctor_set(v___x_2767_, 2, v_v_2775_);
                    leanh::lean_ctor_set(v___x_2767_, 1, v_k_2774_);
                    leanh::lean_ctor_set(v___x_2767_, 0, v___x_2817_);
                    v___x_2819_ = v___x_2767_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2823_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_k_2774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_v_2775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 3, v_l_2776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 4, v_l_2793_);
                    v___x_2819_ = v_reuseFailAlloc_2823_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2820_ = lean_nat_add(v___x_2771_, v_size_2772_);
                if leanh::lean_obj_tag(v_r_2794_) == 0 {
                    v_size_2821_ = leanh::lean_ctor_get(v_r_2794_, 0);
                    leanh::lean_inc(v_size_2821_);
                    v___y_2804_ = v___x_2819_;
                    v___y_2805_ = v___x_2820_;
                    v___y_2806_ = v_size_2821_;
                    state = 5;
                    continue;
                } else {
                    v___x_2822_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2804_ = v___x_2819_;
                    v___y_2805_ = v___x_2820_;
                    v___y_2806_ = v___x_2822_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2844_ = (!leanh::lean_is_exclusive(v_r_2765_)) as u8;
                if v_isSharedCheck_2844_ == 0 {
                    v_unused_2845_ = leanh::lean_ctor_get(v_r_2765_, 4);
                    leanh::lean_dec(v_unused_2845_);
                    v_unused_2846_ = leanh::lean_ctor_get(v_r_2765_, 3);
                    leanh::lean_dec(v_unused_2846_);
                    v_unused_2847_ = leanh::lean_ctor_get(v_r_2765_, 2);
                    leanh::lean_dec(v_unused_2847_);
                    v_unused_2848_ = leanh::lean_ctor_get(v_r_2765_, 1);
                    leanh::lean_dec(v_unused_2848_);
                    v_unused_2849_ = leanh::lean_ctor_get(v_r_2765_, 0);
                    leanh::lean_dec(v_unused_2849_);
                    v___x_2839_ = v_r_2765_;
                    v_isShared_2840_ = v_isSharedCheck_2844_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_2765_);
                    v___x_2839_ = leanh::lean_box(0);
                    v_isShared_2840_ = v_isSharedCheck_2844_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2840_ == 0 {
                    leanh::lean_ctor_set(v___x_2839_, 4, v___x_2837_);
                    leanh::lean_ctor_set(v___x_2839_, 3, v_l_2776_);
                    leanh::lean_ctor_set(v___x_2839_, 2, v_v_2775_);
                    leanh::lean_ctor_set(v___x_2839_, 1, v_k_2774_);
                    leanh::lean_ctor_set(v___x_2839_, 0, v___x_2833_);
                    v___x_2842_ = v___x_2839_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_k_2774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_v_2775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_l_2776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 4, v___x_2837_);
                    v___x_2842_ = v_reuseFailAlloc_2843_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2842_;
            }
            13 => {
                v___x_2864_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_2858_);
                if v_isShared_2863_ == 0 {
                    leanh::lean_ctor_set(v___x_2862_, 3, v_r_2858_);
                    leanh::lean_ctor_set(v___x_2862_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v___x_2862_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v___x_2862_, 0, v___x_2771_);
                    v___x_2866_ = v___x_2862_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2870_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_r_2858_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_r_2858_);
                    v___x_2866_ = v_reuseFailAlloc_2870_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2768_ == 0 {
                    leanh::lean_ctor_set(v___x_2767_, 4, v___x_2866_);
                    leanh::lean_ctor_set(v___x_2767_, 3, v_l_2857_);
                    leanh::lean_ctor_set(v___x_2767_, 2, v_v_2860_);
                    leanh::lean_ctor_set(v___x_2767_, 1, v_k_2859_);
                    leanh::lean_ctor_set(v___x_2767_, 0, v___x_2864_);
                    v___x_2868_ = v___x_2767_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2864_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_k_2859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_v_2860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 3, v_l_2857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 4, v___x_2866_);
                    v___x_2868_ = v_reuseFailAlloc_2869_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2868_;
            }
            16 => {
                v_k_2880_ = leanh::lean_ctor_get(v_r_2874_, 1);
                v_v_2881_ = leanh::lean_ctor_get(v_r_2874_, 2);
                v_isSharedCheck_2895_ = (!leanh::lean_is_exclusive(v_r_2874_)) as u8;
                if v_isSharedCheck_2895_ == 0 {
                    v_unused_2896_ = leanh::lean_ctor_get(v_r_2874_, 4);
                    leanh::lean_dec(v_unused_2896_);
                    v_unused_2897_ = leanh::lean_ctor_get(v_r_2874_, 3);
                    leanh::lean_dec(v_unused_2897_);
                    v_unused_2898_ = leanh::lean_ctor_get(v_r_2874_, 0);
                    leanh::lean_dec(v_unused_2898_);
                    v___x_2883_ = v_r_2874_;
                    v_isShared_2884_ = v_isSharedCheck_2895_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2881_);
                    leanh::lean_inc(v_k_2880_);
                    leanh::lean_dec(v_r_2874_);
                    v___x_2883_ = leanh::lean_box(0);
                    v_isShared_2884_ = v_isSharedCheck_2895_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2885_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2884_ == 0 {
                    leanh::lean_ctor_set(v___x_2883_, 4, v_l_2857_);
                    leanh::lean_ctor_set(v___x_2883_, 3, v_l_2857_);
                    leanh::lean_ctor_set(v___x_2883_, 2, v_v_2876_);
                    leanh::lean_ctor_set(v___x_2883_, 1, v_k_2875_);
                    leanh::lean_ctor_set(v___x_2883_, 0, v___x_2771_);
                    v___x_2887_ = v___x_2883_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_k_2875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_v_2876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 3, v_l_2857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 4, v_l_2857_);
                    v___x_2887_ = v_reuseFailAlloc_2894_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2879_ == 0 {
                    leanh::lean_ctor_set(v___x_2878_, 4, v_l_2857_);
                    leanh::lean_ctor_set(v___x_2878_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v___x_2878_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v___x_2878_, 0, v___x_2771_);
                    v___x_2889_ = v___x_2878_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 3, v_l_2857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 4, v_l_2857_);
                    v___x_2889_ = v_reuseFailAlloc_2893_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2768_ == 0 {
                    leanh::lean_ctor_set(v___x_2767_, 4, v___x_2889_);
                    leanh::lean_ctor_set(v___x_2767_, 3, v___x_2887_);
                    leanh::lean_ctor_set(v___x_2767_, 2, v_v_2881_);
                    leanh::lean_ctor_set(v___x_2767_, 1, v_k_2880_);
                    leanh::lean_ctor_set(v___x_2767_, 0, v___x_2885_);
                    v___x_2891_ = v___x_2767_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2892_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_k_2880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_v_2881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 3, v___x_2887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2892_, 4, v___x_2889_);
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
                v_size_2929_ = leanh::lean_ctor_get(v_l_2916_, 0);
                v_k_2930_ = leanh::lean_ctor_get(v_l_2916_, 1);
                v_v_2931_ = leanh::lean_ctor_get(v_l_2916_, 2);
                v_l_2932_ = leanh::lean_ctor_get(v_l_2916_, 3);
                v_r_2933_ = leanh::lean_ctor_get(v_l_2916_, 4);
                v_size_2934_ = leanh::lean_ctor_get(v_r_2917_, 0);
                v___x_2935_ = leanh::lean_unsigned_to_nat(2);
                v___x_2936_ = lean_nat_mul(v___x_2935_, v_size_2934_);
                v___x_2937_ = lean_nat_dec_lt(v_size_2929_, v___x_2936_);
                leanh::lean_dec(v___x_2936_);
                if v___x_2937_ == 0 {
                    leanh::lean_inc(v_r_2933_);
                    leanh::lean_inc(v_l_2932_);
                    leanh::lean_inc(v_v_2931_);
                    leanh::lean_inc(v_k_2930_);
                    v_isSharedCheck_2965_ = (!leanh::lean_is_exclusive(v_l_2916_)) as u8;
                    if v_isSharedCheck_2965_ == 0 {
                        v_unused_2966_ = leanh::lean_ctor_get(v_l_2916_, 4);
                        leanh::lean_dec(v_unused_2966_);
                        v_unused_2967_ = leanh::lean_ctor_get(v_l_2916_, 3);
                        leanh::lean_dec(v_unused_2967_);
                        v_unused_2968_ = leanh::lean_ctor_get(v_l_2916_, 2);
                        leanh::lean_dec(v_unused_2968_);
                        v_unused_2969_ = leanh::lean_ctor_get(v_l_2916_, 1);
                        leanh::lean_dec(v_unused_2969_);
                        v_unused_2970_ = leanh::lean_ctor_get(v_l_2916_, 0);
                        leanh::lean_dec(v_unused_2970_);
                        v___x_2939_ = v_l_2916_;
                        v_isShared_2940_ = v_isSharedCheck_2965_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_2916_);
                        v___x_2939_ = leanh::lean_box(0);
                        v_isShared_2940_ = v_isSharedCheck_2965_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2767_);
                    v___x_2971_ = lean_nat_add(v___x_2911_, v_size_2912_);
                    v___x_2972_ = lean_nat_add(v___x_2971_, v_size_2913_);
                    leanh::lean_dec(v_size_2913_);
                    v___x_2973_ = lean_nat_add(v___x_2971_, v_size_2929_);
                    leanh::lean_dec(v___x_2971_);
                    leanh::lean_inc_ref(v_l_2764_);
                    if v_isShared_2928_ == 0 {
                        leanh::lean_ctor_set(v___x_2927_, 4, v_l_2916_);
                        leanh::lean_ctor_set(v___x_2927_, 3, v_l_2764_);
                        leanh::lean_ctor_set(v___x_2927_, 2, v_v_2763_);
                        leanh::lean_ctor_set(v___x_2927_, 1, v_k_2762_);
                        leanh::lean_ctor_set(v___x_2927_, 0, v___x_2973_);
                        v___x_2975_ = v___x_2927_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2988_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2973_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_k_2762_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_v_2763_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 3, v_l_2764_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 4, v_l_2916_);
                        v___x_2975_ = v_reuseFailAlloc_2988_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2941_ = lean_nat_add(v___x_2911_, v_size_2912_);
                v___x_2942_ = lean_nat_add(v___x_2941_, v_size_2913_);
                leanh::lean_dec(v_size_2913_);
                if leanh::lean_obj_tag(v_l_2932_) == 0 {
                    v_size_2963_ = leanh::lean_ctor_get(v_l_2932_, 0);
                    leanh::lean_inc(v_size_2963_);
                    v___y_2955_ = v_size_2963_;
                    state = 29;
                    continue;
                } else {
                    v___x_2964_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2955_ = v___x_2964_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2947_ = lean_nat_add(v___y_2945_, v___y_2946_);
                leanh::lean_dec(v___y_2946_);
                leanh::lean_dec(v___y_2945_);
                if v_isShared_2940_ == 0 {
                    leanh::lean_ctor_set(v___x_2939_, 4, v_r_2917_);
                    leanh::lean_ctor_set(v___x_2939_, 3, v_r_2933_);
                    leanh::lean_ctor_set(v___x_2939_, 2, v_v_2915_);
                    leanh::lean_ctor_set(v___x_2939_, 1, v_k_2914_);
                    leanh::lean_ctor_set(v___x_2939_, 0, v___x_2947_);
                    v___x_2949_ = v___x_2939_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_k_2914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_v_2915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 3, v_r_2933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 4, v_r_2917_);
                    v___x_2949_ = v_reuseFailAlloc_2953_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2928_ == 0 {
                    leanh::lean_ctor_set(v___x_2927_, 4, v___x_2949_);
                    leanh::lean_ctor_set(v___x_2927_, 3, v___y_2944_);
                    leanh::lean_ctor_set(v___x_2927_, 2, v_v_2931_);
                    leanh::lean_ctor_set(v___x_2927_, 1, v_k_2930_);
                    leanh::lean_ctor_set(v___x_2927_, 0, v___x_2942_);
                    v___x_2951_ = v___x_2927_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2952_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_k_2930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 2, v_v_2931_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 3, v___y_2944_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2952_, 4, v___x_2949_);
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
                leanh::lean_dec(v___y_2955_);
                leanh::lean_dec(v___x_2941_);
                if v_isShared_2768_ == 0 {
                    leanh::lean_ctor_set(v___x_2767_, 4, v_l_2932_);
                    leanh::lean_ctor_set(v___x_2767_, 0, v___x_2956_);
                    v___x_2958_ = v___x_2767_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2962_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 3, v_l_2764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 4, v_l_2932_);
                    v___x_2958_ = v_reuseFailAlloc_2962_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2959_ = lean_nat_add(v___x_2911_, v_size_2934_);
                if leanh::lean_obj_tag(v_r_2933_) == 0 {
                    v_size_2960_ = leanh::lean_ctor_get(v_r_2933_, 0);
                    leanh::lean_inc(v_size_2960_);
                    v___y_2944_ = v___x_2958_;
                    v___y_2945_ = v___x_2959_;
                    v___y_2946_ = v_size_2960_;
                    state = 26;
                    continue;
                } else {
                    v___x_2961_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2944_ = v___x_2958_;
                    v___y_2945_ = v___x_2959_;
                    v___y_2946_ = v___x_2961_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2982_ = (!leanh::lean_is_exclusive(v_l_2764_)) as u8;
                if v_isSharedCheck_2982_ == 0 {
                    v_unused_2983_ = leanh::lean_ctor_get(v_l_2764_, 4);
                    leanh::lean_dec(v_unused_2983_);
                    v_unused_2984_ = leanh::lean_ctor_get(v_l_2764_, 3);
                    leanh::lean_dec(v_unused_2984_);
                    v_unused_2985_ = leanh::lean_ctor_get(v_l_2764_, 2);
                    leanh::lean_dec(v_unused_2985_);
                    v_unused_2986_ = leanh::lean_ctor_get(v_l_2764_, 1);
                    leanh::lean_dec(v_unused_2986_);
                    v_unused_2987_ = leanh::lean_ctor_get(v_l_2764_, 0);
                    leanh::lean_dec(v_unused_2987_);
                    v___x_2977_ = v_l_2764_;
                    v_isShared_2978_ = v_isSharedCheck_2982_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_2764_);
                    v___x_2977_ = leanh::lean_box(0);
                    v_isShared_2978_ = v_isSharedCheck_2982_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2978_ == 0 {
                    leanh::lean_ctor_set(v___x_2977_, 4, v_r_2917_);
                    leanh::lean_ctor_set(v___x_2977_, 3, v___x_2975_);
                    leanh::lean_ctor_set(v___x_2977_, 2, v_v_2915_);
                    leanh::lean_ctor_set(v___x_2977_, 1, v_k_2914_);
                    leanh::lean_ctor_set(v___x_2977_, 0, v___x_2972_);
                    v___x_2980_ = v___x_2977_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_k_2914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_v_2915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 3, v___x_2975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 4, v_r_2917_);
                    v___x_2980_ = v_reuseFailAlloc_2981_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2980_;
            }
            34 => {
                v_k_3002_ = leanh::lean_ctor_get(v_l_2995_, 1);
                v_v_3003_ = leanh::lean_ctor_get(v_l_2995_, 2);
                v_isSharedCheck_3017_ = (!leanh::lean_is_exclusive(v_l_2995_)) as u8;
                if v_isSharedCheck_3017_ == 0 {
                    v_unused_3018_ = leanh::lean_ctor_get(v_l_2995_, 4);
                    leanh::lean_dec(v_unused_3018_);
                    v_unused_3019_ = leanh::lean_ctor_get(v_l_2995_, 3);
                    leanh::lean_dec(v_unused_3019_);
                    v_unused_3020_ = leanh::lean_ctor_get(v_l_2995_, 0);
                    leanh::lean_dec(v_unused_3020_);
                    v___x_3005_ = v_l_2995_;
                    v_isShared_3006_ = v_isSharedCheck_3017_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3003_);
                    leanh::lean_inc(v_k_3002_);
                    leanh::lean_dec(v_l_2995_);
                    v___x_3005_ = leanh::lean_box(0);
                    v_isShared_3006_ = v_isSharedCheck_3017_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3007_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_2996_, 2);
                if v_isShared_3006_ == 0 {
                    leanh::lean_ctor_set(v___x_3005_, 4, v_r_2996_);
                    leanh::lean_ctor_set(v___x_3005_, 3, v_r_2996_);
                    leanh::lean_ctor_set(v___x_3005_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v___x_3005_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v___x_3005_, 0, v___x_2911_);
                    v___x_3009_ = v___x_3005_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3016_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_2911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 3, v_r_2996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 4, v_r_2996_);
                    v___x_3009_ = v_reuseFailAlloc_3016_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_2996_);
                if v_isShared_3001_ == 0 {
                    leanh::lean_ctor_set(v___x_3000_, 3, v_r_2996_);
                    leanh::lean_ctor_set(v___x_3000_, 0, v___x_2911_);
                    v___x_3011_ = v___x_3000_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3015_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_2911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 1, v_k_2997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 2, v_v_2998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 3, v_r_2996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 4, v_r_2996_);
                    v___x_3011_ = v_reuseFailAlloc_3015_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2768_ == 0 {
                    leanh::lean_ctor_set(v___x_2767_, 4, v___x_3011_);
                    leanh::lean_ctor_set(v___x_2767_, 3, v___x_3009_);
                    leanh::lean_ctor_set(v___x_2767_, 2, v_v_3003_);
                    leanh::lean_ctor_set(v___x_2767_, 1, v_k_3002_);
                    leanh::lean_ctor_set(v___x_2767_, 0, v___x_3007_);
                    v___x_3013_ = v___x_2767_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_k_3002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_v_3003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 3, v___x_3009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 4, v___x_3011_);
                    v___x_3013_ = v_reuseFailAlloc_3014_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3013_;
            }
            39 => {
                v___x_3030_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3029_ == 0 {
                    leanh::lean_ctor_set(v___x_3028_, 4, v_l_2995_);
                    leanh::lean_ctor_set(v___x_3028_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v___x_3028_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v___x_3028_, 0, v___x_2911_);
                    v___x_3032_ = v___x_3028_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_2911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_2762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_2763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_l_2995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_l_2995_);
                    v___x_3032_ = v_reuseFailAlloc_3036_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2768_ == 0 {
                    leanh::lean_ctor_set(v___x_2767_, 4, v_r_3024_);
                    leanh::lean_ctor_set(v___x_2767_, 3, v___x_3032_);
                    leanh::lean_ctor_set(v___x_2767_, 2, v_v_3026_);
                    leanh::lean_ctor_set(v___x_2767_, 1, v_k_3025_);
                    leanh::lean_ctor_set(v___x_2767_, 0, v___x_3030_);
                    v___x_3034_ = v___x_2767_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_k_3025_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_v_3026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 3, v___x_3032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 4, v_r_3024_);
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
pub unsafe fn _init_l_Lake_LeanExe_initFacetConfigs___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = leanh::lean_box(1);
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
pub unsafe fn _init_l_Lake_LeanExe_initFacetConfigs___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3052_ = leanh::lean_obj_once(
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
pub unsafe fn _init_l_Lake_LeanExe_initFacetConfigs() -> *mut leanh::LeanObject {
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3056_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExe_initFacetConfigs___closed__1),
        core::ptr::addr_of_mut!(l_Lake_LeanExe_initFacetConfigs___closed__1_once),
        _init_l_Lake_LeanExe_initFacetConfigs___closed__1,
    );
    return v___x_3056_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(
    mut v_00_u03b2_3057_: *mut leanh::LeanObject,
    mut v_k_3058_: *mut leanh::LeanObject,
    mut v_v_3059_: *mut leanh::LeanObject,
    mut v_t_3060_: *mut leanh::LeanObject,
    mut v_hl_3061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3062_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(
            v_k_3058_, v_v_3059_, v_t_3060_,
        );
    return v___x_3062_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Executable(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_FacetConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Register(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Target_Fetch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Common(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13 = _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13();
    leanh::lean_mark_persistent(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13);
    l_Lake_LeanExe_exeFacetConfig = _init_l_Lake_LeanExe_exeFacetConfig();
    leanh::lean_mark_persistent(l_Lake_LeanExe_exeFacetConfig);
    l_Lake_LeanExe_defaultFacetConfig = _init_l_Lake_LeanExe_defaultFacetConfig();
    leanh::lean_mark_persistent(l_Lake_LeanExe_defaultFacetConfig);
    l_Lake_LeanExe_initFacetConfigs = _init_l_Lake_LeanExe_initFacetConfigs();
    leanh::lean_mark_persistent(l_Lake_LeanExe_initFacetConfigs);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Executable(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Executable(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_FacetConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Register(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Target_Fetch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Common(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Infos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Executable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Executable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Executable(builtin);
}