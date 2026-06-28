// Lean compiler output
// Module: Lake.Build.ExternLib
// Imports: Lake.Config.FacetConfig Lake.Build.Job.Monad Lake.Build.Job.Register Lake.Build.Common Lake.Build.Infos
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_fileStem, l_System_FilePath_withExtension,
};
use crate::r#gen::Init::System::Platform::{l_System_Platform_isOSX, l_System_Platform_isWindows};
use crate::r#gen::Lake::Build::Actions::l_Lake_compileSharedLib;
use crate::r#gen::Lake::Build::Common::{
    initialize_Lake_Build_Common, l_Lake_buildFileUnlessUpToDate_x27, l_Lake_platformTrace,
    runtime_initialize_Lake_Build_Common,
};
use crate::r#gen::Lake::Build::Data::{l_Lake_instDataKindDynlib, l_Lake_instDataKindFilePath};
use crate::r#gen::Lake::Build::Facets::{
    l_Lake_ExternLib_defaultFacet, l_Lake_ExternLib_dynlibFacet, l_Lake_ExternLib_sharedFacet,
    l_Lake_ExternLib_staticFacet,
};
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_Job_toOpaque___redArg;
use crate::r#gen::Lake::Build::Job::Monad::{
    initialize_Lake_Build_Job_Monad, l_Lake_Job_mapM___redArg,
    runtime_initialize_Lake_Build_Job_Monad,
};
use crate::r#gen::Lake::Build::Job::Register::{
    initialize_Lake_Build_Job_Register, l_Lake_Job_renew___redArg, l_Lake_ensureJob___redArg,
    runtime_initialize_Lake_Build_Job_Register,
};
use crate::r#gen::Lake::Build::Trace::{
    l_Lake_BuildTrace_mix, l_Lake_BuildTrace_nil, l_Lake_Hash_nil,
};
use crate::r#gen::Lake::Config::FacetConfig::{
    initialize_Lake_Config_FacetConfig, runtime_initialize_Lake_Config_FacetConfig,
};
use crate::r#gen::Lake::Config::Kinds::l_Lake_ExternLib_keyword;
use crate::r#gen::Lake::Util::FilePath::l_Lake_mkRelPathString;
use crate::r#gen::Lake::Util::NativeLib::l_Lake_sharedLibExt;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_string_hash,
    lean_string_utf8_byte_size, lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
pub static l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 116, 97, 116, 105, 99, 0],
};
static mut l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_ExternLib_staticFacetConfig___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_ExternLib_staticFacetConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_staticFacetConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ExternLib_staticFacetConfig___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_ExternLib_staticFacetConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_staticFacetConfig___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_ExternLib_staticFacetConfig___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ExternLib_staticFacetConfig___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_ExternLib_staticFacetConfig: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 76, 0],
};
static mut l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        45, 87, 108, 44, 45, 45, 119, 104, 111, 108, 101, 45, 97, 114, 99, 104, 105, 118, 101, 0,
    ],
};
static mut l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        45, 87, 108, 44, 45, 45, 110, 111, 45, 119, 104, 111, 108, 101, 45, 97, 114, 99, 104, 105,
        118, 101, 0,
    ],
};
static mut l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        45, 87, 108, 44, 45, 102, 111, 114, 99, 101, 95, 108, 111, 97, 100, 44, 0,
    ],
};
static mut l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [91, 93, 0],
};
static mut l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [91, 0],
};
static mut l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [112, 117, 114, 101, 58, 32, 0],
};
static mut l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [35, 0],
};
static mut l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2_value:
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
static mut l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 110, 105, 108, 62, 0]};
static mut l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_ExternLib_sharedFacetConfig___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_ExternLib_sharedFacetConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_sharedFacetConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_ExternLib_sharedFacetConfig___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ExternLib_sharedFacetConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_ExternLib_sharedFacetConfig: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 104, 97, 114, 101, 100, 32, 108, 105, 98, 114, 97, 114, 121, 32, 96, 0]};
static mut l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1_value: crate::leanh::LeanStringObject<59> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 59, m_capacity: 59, m_length: 58, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 116, 97, 114, 116, 32, 119, 105, 116, 104, 32, 96, 108, 105, 98, 96, 59, 32, 116, 104, 105, 115, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 111, 110, 32, 85, 110, 105, 120, 0]};
static mut l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 105, 98, 0]};
static mut l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [96, 32, 104, 97, 115, 32, 110, 111, 32, 102, 105, 108, 101, 32, 110, 97, 109, 101, 0]};
static mut l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [58, 100, 121, 110, 108, 105, 98, 0],
};
static mut l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_ExternLib_dynlibFacetConfig___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_ExternLib_dynlibFacetConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_dynlibFacetConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ExternLib_dynlibFacetConfig___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_ExternLib_dynlibFacetConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_dynlibFacetConfig___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_ExternLib_dynlibFacetConfig___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ExternLib_dynlibFacetConfig___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_ExternLib_dynlibFacetConfig: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_ExternLib_defaultFacetConfig___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_ExternLib_defaultFacetConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_defaultFacetConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_ExternLib_defaultFacetConfig___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ExternLib_defaultFacetConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_ExternLib_defaultFacetConfig: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_ExternLib_initFacetConfigs___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ExternLib_initFacetConfigs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_ExternLib_initFacetConfigs___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ExternLib_initFacetConfigs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_ExternLib_initFacetConfigs___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ExternLib_initFacetConfigs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_ExternLib_initFacetConfigs___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ExternLib_initFacetConfigs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_ExternLib_initFacetConfigs: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(
    mut v___x_1066_: *mut crate::leanh::LeanObject,
    mut v_config_1067_: *mut crate::leanh::LeanObject,
    mut v___y_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
    mut v___y_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut v_a_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1090_: u8 = 0;
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___y_1072_);
                crate::leanh::lean_inc(v___y_1071_);
                crate::leanh::lean_inc(v___y_1070_);
                crate::leanh::lean_inc(v___y_1069_);
                v___x_1075_ = crate::leanh::lean_apply_7(
                    v___y_1068_,
                    v___x_1066_,
                    v___y_1069_,
                    v___y_1070_,
                    v___y_1071_,
                    v___y_1072_,
                    v___y_1073_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1075_) == 0 {
                    v_a_1076_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                    v_a_1077_ = crate::leanh::lean_ctor_get(v___x_1075_, 1);
                    v_isSharedCheck_1085_ = (!crate::leanh::lean_is_exclusive(v___x_1075_)) as u8;
                    if v_isSharedCheck_1085_ == 0 {
                        v___x_1079_ = v___x_1075_;
                        v_isShared_1080_ = v_isSharedCheck_1085_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1077_);
                        crate::leanh::lean_inc(v_a_1076_);
                        crate::leanh::lean_dec(v___x_1075_);
                        v___x_1079_ = crate::leanh::lean_box(0);
                        v_isShared_1080_ = v_isSharedCheck_1085_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_config_1067_);
                    v_a_1086_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                    v_a_1087_ = crate::leanh::lean_ctor_get(v___x_1075_, 1);
                    v_isSharedCheck_1094_ = (!crate::leanh::lean_is_exclusive(v___x_1075_)) as u8;
                    if v_isSharedCheck_1094_ == 0 {
                        v___x_1089_ = v___x_1075_;
                        v_isShared_1090_ = v_isSharedCheck_1094_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1087_);
                        crate::leanh::lean_inc(v_a_1086_);
                        crate::leanh::lean_dec(v___x_1075_);
                        v___x_1089_ = crate::leanh::lean_box(0);
                        v_isShared_1090_ = v_isSharedCheck_1094_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1081_ = crate::leanh::lean_apply_1(v_config_1067_, v_a_1076_);
                if v_isShared_1080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1079_, 0, v___x_1081_);
                    v___x_1083_ = v___x_1079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1084_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_a_1077_);
                    v___x_1083_ = v_reuseFailAlloc_1084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1083_;
            }
            3 => {
                if v_isShared_1090_ == 0 {
                    v___x_1092_ = v___x_1089_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1093_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_a_1087_);
                    v___x_1092_ = v_reuseFailAlloc_1093_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed(
    mut v___x_1095_: *mut crate::leanh::LeanObject,
    mut v_config_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
    mut v___y_1098_: *mut crate::leanh::LeanObject,
    mut v___y_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
    mut v___y_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(
        v___x_1095_,
        v_config_1096_,
        v___y_1097_,
        v___y_1098_,
        v___y_1099_,
        v___y_1100_,
        v___y_1101_,
        v___y_1102_,
    );
    crate::leanh::lean_dec_ref(v___y_1101_);
    crate::leanh::lean_dec(v___y_1100_);
    crate::leanh::lean_dec(v___y_1099_);
    crate::leanh::lean_dec(v___y_1098_);
    return v_res_1104_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(
    mut v_lib_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: u8 = 0;
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1130_: u8 = 0;
    let mut v_task_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1135_: u8 = 0;
    let mut v_registeredJobs_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: u8 = 0;
    let mut v_job_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut v_unused_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1115_ = crate::leanh::lean_ctor_get(v_lib_1107_, 0);
                crate::leanh::lean_inc_ref(v_pkg_1115_);
                v_name_1116_ = crate::leanh::lean_ctor_get(v_lib_1107_, 1);
                crate::leanh::lean_inc(v_name_1116_);
                v_config_1117_ = crate::leanh::lean_ctor_get(v_lib_1107_, 2);
                crate::leanh::lean_inc(v_config_1117_);
                crate::leanh::lean_dec_ref(v_lib_1107_);
                v___x_1118_ = l_Lake_instDataKindFilePath;
                v___x_1119_ =
                    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
                v___x_1120_ = l_Lean_Name_str___override(v_name_1116_, v___x_1119_);
                v___x_1121_ = 1;
                crate::leanh::lean_inc(v___x_1120_);
                v___x_1122_ = l_Lean_Name_toString(v___x_1120_, v___x_1121_);
                v___x_1123_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1123_, 0, v_pkg_1115_);
                crate::leanh::lean_ctor_set(v___x_1123_, 1, v___x_1120_);
                v___f_1124_ = crate::leanh::lean_alloc_closure(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___f_1124_, 0, v___x_1123_);
                crate::leanh::lean_closure_set(v___f_1124_, 1, v_config_1117_);
                v___x_1125_ = l_Lake_ensureJob___redArg(
                    v___x_1118_,
                    v___f_1124_,
                    v_a_1108_,
                    v_a_1109_,
                    v_a_1110_,
                    v_a_1111_,
                    v_a_1112_,
                    v_a_1113_,
                );
                if crate::leanh::lean_obj_tag(v___x_1125_) == 0 {
                    v_a_1126_ = crate::leanh::lean_ctor_get(v___x_1125_, 0);
                    v_a_1127_ = crate::leanh::lean_ctor_get(v___x_1125_, 1);
                    v_isSharedCheck_1153_ = (!crate::leanh::lean_is_exclusive(v___x_1125_)) as u8;
                    if v_isSharedCheck_1153_ == 0 {
                        v___x_1129_ = v___x_1125_;
                        v_isShared_1130_ = v_isSharedCheck_1153_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1127_);
                        crate::leanh::lean_inc(v_a_1126_);
                        crate::leanh::lean_dec(v___x_1125_);
                        v___x_1129_ = crate::leanh::lean_box(0);
                        v_isShared_1130_ = v_isSharedCheck_1153_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1122_);
                    return v___x_1125_;
                }
            }
            1 => {
                v_task_1131_ = crate::leanh::lean_ctor_get(v_a_1126_, 0);
                v_kind_1132_ = crate::leanh::lean_ctor_get(v_a_1126_, 1);
                v_isSharedCheck_1151_ = (!crate::leanh::lean_is_exclusive(v_a_1126_)) as u8;
                if v_isSharedCheck_1151_ == 0 {
                    v_unused_1152_ = crate::leanh::lean_ctor_get(v_a_1126_, 2);
                    crate::leanh::lean_dec(v_unused_1152_);
                    v___x_1134_ = v_a_1126_;
                    v_isShared_1135_ = v_isSharedCheck_1151_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_1132_);
                    crate::leanh::lean_inc(v_task_1131_);
                    crate::leanh::lean_dec(v_a_1126_);
                    v___x_1134_ = crate::leanh::lean_box(0);
                    v_isShared_1135_ = v_isSharedCheck_1151_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_1136_ = crate::leanh::lean_ctor_get(v_a_1112_, 3);
                v___x_1137_ = lean_st_ref_take(v_registeredJobs_1136_);
                v___x_1138_ =
                    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1;
                v___x_1139_ = lean_string_append(v___x_1122_, v___x_1138_);
                v___x_1140_ = 0;
                if v_isShared_1135_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1134_, 2, v___x_1139_);
                    v_job_1142_ = v___x_1134_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1150_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_task_1131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_kind_1132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1150_, 2, v___x_1139_);
                    v_job_1142_ = v_reuseFailAlloc_1150_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_1142_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1140_,
                );
                crate::leanh::lean_inc_ref(v_job_1142_);
                v___x_1143_ = l_Lake_Job_toOpaque___redArg(v_job_1142_);
                v___x_1144_ = lean_array_push(v___x_1137_, v___x_1143_);
                v___x_1145_ = lean_st_ref_set(v_registeredJobs_1136_, v___x_1144_);
                v___x_1146_ = l_Lake_Job_renew___redArg(v_job_1142_);
                if v_isShared_1130_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1129_, 0, v___x_1146_);
                    v___x_1148_ = v___x_1129_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_a_1127_);
                    v___x_1148_ = v_reuseFailAlloc_1149_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed(
    mut v_lib_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_a_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
    mut v_a_1159_: *mut crate::leanh::LeanObject,
    mut v_a_1160_: *mut crate::leanh::LeanObject,
    mut v_a_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(
        v_lib_1154_,
        v_a_1155_,
        v_a_1156_,
        v_a_1157_,
        v_a_1158_,
        v_a_1159_,
        v_a_1160_,
    );
    crate::leanh::lean_dec_ref(v_a_1159_);
    crate::leanh::lean_dec(v_a_1158_);
    crate::leanh::lean_dec(v_a_1157_);
    crate::leanh::lean_dec(v_a_1156_);
    return v_res_1162_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(
    mut v_fmt_1163_: u8,
    mut v_a_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_fmt_1163_ == 0 {
        return v_a_1164_;
    } else {
        let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1165_ = l_Lake_mkRelPathString(v_a_1164_);
        v___x_1166_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1166_, 0, v___x_1165_);
        v___x_1167_ = l_Lean_Json_compress(v___x_1166_);
        return v___x_1167_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed(
    mut v_fmt_1168_: *mut crate::leanh::LeanObject,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fmt_boxed_1170_: u8 = 0;
    let mut v_res_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fmt_boxed_1170_ = (crate::leanh::lean_unbox(v_fmt_1168_) as u8);
    v_res_1171_ = l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(
        v_fmt_boxed_1170_,
        v_a_1169_,
    );
    return v_res_1171_;
}
pub unsafe fn _init_l_Lake_ExternLib_staticFacetConfig___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___f_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1174_ = l_Lake_ExternLib_staticFacetConfig___closed__0;
    v___x_1175_ = 1;
    v___x_1176_ = l_Lake_instDataKindFilePath;
    v___x_1177_ = l_Lake_ExternLib_staticFacetConfig___closed__1;
    v___x_1178_ = l_Lake_ExternLib_keyword;
    v___x_1179_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1179_, 0, v___x_1178_);
    crate::leanh::lean_ctor_set(v___x_1179_, 1, v___x_1177_);
    crate::leanh::lean_ctor_set(v___x_1179_, 2, v___x_1176_);
    crate::leanh::lean_ctor_set(v___x_1179_, 3, v___f_1174_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1179_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_1175_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1179_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v___x_1175_,
    );
    return v___x_1179_;
}
pub unsafe fn _init_l_Lake_ExternLib_staticFacetConfig() -> *mut crate::leanh::LeanObject {
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1180_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ExternLib_staticFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_ExternLib_staticFacetConfig___closed__2_once),
        _init_l_Lake_ExternLib_staticFacetConfig___closed__2,
    );
    return v___x_1180_;
}
pub unsafe fn _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0;
    v___x_1183_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1184_ = lean_mk_empty_array_with_capacity(v___x_1183_);
    v___x_1185_ = lean_array_push(v___x_1184_, v___x_1182_);
    return v___x_1185_;
}
pub unsafe fn _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1188_ = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2;
    v___x_1189_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1190_ = lean_mk_empty_array_with_capacity(v___x_1189_);
    v___x_1191_ = lean_array_push(v___x_1190_, v___x_1188_);
    return v___x_1191_;
}
pub unsafe fn l_Lake_buildLeanSharedLibOfStatic___lam__0(
    mut v_weakArgs_1193_: *mut crate::leanh::LeanObject,
    mut v_traceArgs_1194_: *mut crate::leanh::LeanObject,
    mut v___x_1195_: *mut crate::leanh::LeanObject,
    mut v_staticLib_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
    mut v___y_1198_: *mut crate::leanh::LeanObject,
    mut v___y_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toContext_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1207_: u8 = 0;
    let mut v_wantsRebuild_1208_: u8 = 0;
    let mut v_trace_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1213_: u8 = 0;
    let mut v_lean_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cc_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1238_: u8 = 0;
    let mut v_a_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1243_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1250_: u8 = 0;
    let mut v___x_1251_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toContext_1204_ = crate::leanh::lean_ctor_get(v___y_1201_, 1);
                v_lakeEnv_1205_ = crate::leanh::lean_ctor_get(v_toContext_1204_, 0);
                v_log_1206_ = crate::leanh::lean_ctor_get(v___y_1202_, 0);
                v_action_1207_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1202_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1208_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1202_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1209_ = crate::leanh::lean_ctor_get(v___y_1202_, 1);
                v_buildTime_1210_ = crate::leanh::lean_ctor_get(v___y_1202_, 2);
                v_isSharedCheck_1261_ = (!crate::leanh::lean_is_exclusive(v___y_1202_)) as u8;
                if v_isSharedCheck_1261_ == 0 {
                    v___x_1212_ = v___y_1202_;
                    v_isShared_1213_ = v_isSharedCheck_1261_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_1210_);
                    crate::leanh::lean_inc(v_trace_1209_);
                    crate::leanh::lean_inc(v_log_1206_);
                    crate::leanh::lean_dec(v___y_1202_);
                    v___x_1212_ = crate::leanh::lean_box(0);
                    v_isShared_1213_ = v_isSharedCheck_1261_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_lean_1214_ = crate::leanh::lean_ctor_get(v_lakeEnv_1205_, 1);
                v___x_1251_ = l_System_Platform_isOSX;
                if v___x_1251_ == 0 {
                    v___x_1252_ = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3;
                    v___x_1253_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4_once
                        ),
                        _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4,
                    );
                    v___x_1254_ = lean_array_push(v___x_1253_, v_staticLib_1196_);
                    v___x_1255_ = lean_array_push(v___x_1254_, v___x_1252_);
                    v___y_1216_ = v___x_1255_;
                    state = 2;
                    continue;
                } else {
                    v___x_1256_ = l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5;
                    v___x_1257_ = lean_string_append(v___x_1256_, v_staticLib_1196_);
                    crate::leanh::lean_dec_ref(v_staticLib_1196_);
                    v___x_1258_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1259_ = lean_mk_empty_array_with_capacity(v___x_1258_);
                    v___x_1260_ = lean_array_push(v___x_1259_, v___x_1257_);
                    v___y_1216_ = v___x_1260_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_leanLibDir_1217_ = crate::leanh::lean_ctor_get(v_lean_1214_, 3);
                v_cc_1218_ = crate::leanh::lean_ctor_get(v_lean_1214_, 14);
                v_ccLinkSharedFlags_1219_ = crate::leanh::lean_ctor_get(v_lean_1214_, 20);
                v___x_1220_ = l_Array_append___redArg(v___y_1216_, v_weakArgs_1193_);
                v___x_1221_ = l_Array_append___redArg(v___x_1220_, v_traceArgs_1194_);
                v___x_1222_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1_once
                    ),
                    _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1,
                );
                crate::leanh::lean_inc_ref(v_leanLibDir_1217_);
                v___x_1223_ = lean_array_push(v___x_1222_, v_leanLibDir_1217_);
                v___x_1224_ = l_Array_append___redArg(v___x_1221_, v___x_1223_);
                crate::leanh::lean_dec_ref(v___x_1223_);
                v___x_1225_ = l_Array_append___redArg(v___x_1224_, v_ccLinkSharedFlags_1219_);
                crate::leanh::lean_inc_ref(v_cc_1218_);
                v___x_1226_ =
                    l_Lake_compileSharedLib(v___x_1195_, v___x_1225_, v_cc_1218_, v_log_1206_);
                crate::leanh::lean_dec_ref(v___x_1225_);
                if crate::leanh::lean_obj_tag(v___x_1226_) == 0 {
                    v_a_1227_ = crate::leanh::lean_ctor_get(v___x_1226_, 0);
                    v_a_1228_ = crate::leanh::lean_ctor_get(v___x_1226_, 1);
                    v_isSharedCheck_1238_ = (!crate::leanh::lean_is_exclusive(v___x_1226_)) as u8;
                    if v_isSharedCheck_1238_ == 0 {
                        v___x_1230_ = v___x_1226_;
                        v_isShared_1231_ = v_isSharedCheck_1238_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1228_);
                        crate::leanh::lean_inc(v_a_1227_);
                        crate::leanh::lean_dec(v___x_1226_);
                        v___x_1230_ = crate::leanh::lean_box(0);
                        v_isShared_1231_ = v_isSharedCheck_1238_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1239_ = crate::leanh::lean_ctor_get(v___x_1226_, 0);
                    v_a_1240_ = crate::leanh::lean_ctor_get(v___x_1226_, 1);
                    v_isSharedCheck_1250_ = (!crate::leanh::lean_is_exclusive(v___x_1226_)) as u8;
                    if v_isSharedCheck_1250_ == 0 {
                        v___x_1242_ = v___x_1226_;
                        v_isShared_1243_ = v_isSharedCheck_1250_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1240_);
                        crate::leanh::lean_inc(v_a_1239_);
                        crate::leanh::lean_dec(v___x_1226_);
                        v___x_1242_ = crate::leanh::lean_box(0);
                        v_isShared_1243_ = v_isSharedCheck_1250_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1212_, 0, v_a_1228_);
                    v___x_1233_ = v___x_1212_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1237_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_trace_1209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_buildTime_1210_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1237_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1207_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1237_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1208_,
                    );
                    v___x_1233_ = v_reuseFailAlloc_1237_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1230_, 1, v___x_1233_);
                    v___x_1235_ = v___x_1230_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1233_);
                    v___x_1235_ = v_reuseFailAlloc_1236_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1235_;
            }
            6 => {
                if v_isShared_1213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1212_, 0, v_a_1240_);
                    v___x_1245_ = v___x_1212_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1249_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_trace_1209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_buildTime_1210_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1249_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1207_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1249_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1208_,
                    );
                    v___x_1245_ = v_reuseFailAlloc_1249_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1243_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1242_, 1, v___x_1245_);
                    v___x_1247_ = v___x_1242_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1248_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1245_);
                    v___x_1247_ = v_reuseFailAlloc_1248_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(
    mut v_weakArgs_1262_: *mut crate::leanh::LeanObject,
    mut v_traceArgs_1263_: *mut crate::leanh::LeanObject,
    mut v___x_1264_: *mut crate::leanh::LeanObject,
    mut v_staticLib_1265_: *mut crate::leanh::LeanObject,
    mut v___y_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1273_ = l_Lake_buildLeanSharedLibOfStatic___lam__0(
        v_weakArgs_1262_,
        v_traceArgs_1263_,
        v___x_1264_,
        v_staticLib_1265_,
        v___y_1266_,
        v___y_1267_,
        v___y_1268_,
        v___y_1269_,
        v___y_1270_,
        v___y_1271_,
    );
    crate::leanh::lean_dec_ref(v___y_1270_);
    crate::leanh::lean_dec(v___y_1269_);
    crate::leanh::lean_dec(v___y_1268_);
    crate::leanh::lean_dec(v___y_1267_);
    crate::leanh::lean_dec_ref(v___y_1266_);
    crate::leanh::lean_dec_ref(v_traceArgs_1263_);
    crate::leanh::lean_dec_ref(v_weakArgs_1262_);
    return v_res_1273_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(
    mut v_as_1274_: *mut crate::leanh::LeanObject,
    mut v_i_1275_: usize,
    mut v_stop_1276_: usize,
    mut v_b_1277_: u64,
) -> u64 {
    let mut v___x_1278_: u8 = 0;
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u64 = 0;
    let mut v___x_1281_: u64 = 0;
    let mut v___x_1282_: u64 = 0;
    let mut v___x_1283_: u64 = 0;
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1278_ = lean_usize_dec_eq(v_i_1275_, v_stop_1276_);
                if v___x_1278_ == 0 {
                    v___x_1279_ = lean_array_uget_borrowed(v_as_1274_, v_i_1275_);
                    v___x_1280_ = l_Lake_Hash_nil;
                    v___x_1281_ = lean_string_hash(v___x_1279_);
                    v___x_1282_ = lean_uint64_mix_hash(v___x_1280_, v___x_1281_);
                    v___x_1283_ = lean_uint64_mix_hash(v_b_1277_, v___x_1282_);
                    v___x_1284_ = 1usize;
                    v___x_1285_ = lean_usize_add(v_i_1275_, v___x_1284_);
                    v_i_1275_ = v___x_1285_;
                    v_b_1277_ = v___x_1283_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1277_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1___boxed(
    mut v_as_1287_: *mut crate::leanh::LeanObject,
    mut v_i_1288_: *mut crate::leanh::LeanObject,
    mut v_stop_1289_: *mut crate::leanh::LeanObject,
    mut v_b_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1291_: usize = 0;
    let mut v_stop_boxed_1292_: usize = 0;
    let mut v_b_boxed_1293_: u64 = 0;
    let mut v_res_1294_: u64 = 0;
    let mut v_r_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1291_ = crate::leanh::lean_unbox_usize(v_i_1288_);
    crate::leanh::lean_dec(v_i_1288_);
    v_stop_boxed_1292_ = crate::leanh::lean_unbox_usize(v_stop_1289_);
    crate::leanh::lean_dec(v_stop_1289_);
    v_b_boxed_1293_ = crate::leanh::lean_unbox_uint64(v_b_1290_);
    crate::leanh::lean_dec_ref(v_b_1290_);
    v_res_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_as_1287_, v_i_boxed_1291_, v_stop_boxed_1292_, v_b_boxed_1293_);
    crate::leanh::lean_dec_ref(v_as_1287_);
    v_r_1295_ = crate::leanh::lean_box_uint64(v_res_1294_);
    return v_r_1295_;
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(
    mut v_x_1297_: *mut crate::leanh::LeanObject,
    mut v_x_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1298_) == 0 {
                    return v_x_1297_;
                } else {
                    v_head_1299_ = crate::leanh::lean_ctor_get(v_x_1298_, 0);
                    v_tail_1300_ = crate::leanh::lean_ctor_get(v_x_1298_, 1);
                    v___x_1301_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0;
                    v___x_1302_ = lean_string_append(v_x_1297_, v___x_1301_);
                    v___x_1303_ = lean_string_append(v___x_1302_, v_head_1299_);
                    v_x_1297_ = v___x_1303_;
                    v_x_1298_ = v_tail_1300_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___boxed(
    mut v_x_1305_: *mut crate::leanh::LeanObject,
    mut v_x_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v_x_1305_, v_x_1306_);
    crate::leanh::lean_dec(v_x_1306_);
    return v_res_1307_;
}
pub unsafe fn l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(
    mut v_x_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1311_) == 0 {
        let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1312_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0;
        return v___x_1312_;
    } else {
        let mut v_tail_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1313_ = crate::leanh::lean_ctor_get(v_x_1311_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1313_) == 0 {
            let mut v_head_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_1314_ = crate::leanh::lean_ctor_get(v_x_1311_, 0);
            v___x_1315_ =
                l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1;
            v___x_1316_ = lean_string_append(v___x_1315_, v_head_1314_);
            v___x_1317_ =
                l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2;
            v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
            return v___x_1318_;
        } else {
            let mut v_head_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1323_: u32 = 0;
            let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_1319_ = crate::leanh::lean_ctor_get(v_x_1311_, 0);
            v___x_1320_ =
                l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1;
            v___x_1321_ = lean_string_append(v___x_1320_, v_head_1319_);
            v___x_1322_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v___x_1321_, v_tail_1313_);
            v___x_1323_ = 93;
            v___x_1324_ = lean_string_push(v___x_1322_, v___x_1323_);
            return v___x_1324_;
        }
    }
}
pub unsafe fn l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___boxed(
    mut v_x_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v_x_1325_);
    crate::leanh::lean_dec(v_x_1325_);
    return v_res_1326_;
}
pub unsafe fn _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1332_ = lean_nat_to_int(v___x_1331_);
    return v___x_1332_;
}
pub unsafe fn _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: u32 = 0;
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = 0;
    v___x_1334_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3),
        core::ptr::addr_of_mut!(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3_once),
        _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3,
    );
    v___x_1335_ = crate::leanh::lean_alloc_ctor(0, 1, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_1335_, 0, v___x_1334_);
    crate::leanh::lean_ctor_set_uint32(
        v___x_1335_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1333_,
    );
    return v___x_1335_;
}
pub unsafe fn l_Lake_buildLeanSharedLibOfStatic___lam__1(
    mut v_traceArgs_1336_: *mut crate::leanh::LeanObject,
    mut v_weakArgs_1337_: *mut crate::leanh::LeanObject,
    mut v_staticLib_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1347_: u8 = 0;
    let mut v_wantsRebuild_1348_: u8 = 0;
    let mut v_trace_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1353_: u8 = 0;
    let mut v_leanTrace_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: u64 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1384_: u8 = 0;
    let mut v_unused_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1394_: u8 = 0;
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u64 = 0;
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: usize = 0;
    let mut v___x_1402_: usize = 0;
    let mut v___x_1403_: u64 = 0;
    let mut v___x_1404_: usize = 0;
    let mut v___x_1405_: usize = 0;
    let mut v___x_1406_: u64 = 0;
    let mut v_isSharedCheck_1407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_1346_ = crate::leanh::lean_ctor_get(v___y_1344_, 0);
                v_action_1347_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1344_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1348_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1344_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1349_ = crate::leanh::lean_ctor_get(v___y_1344_, 1);
                v_buildTime_1350_ = crate::leanh::lean_ctor_get(v___y_1344_, 2);
                v_isSharedCheck_1407_ = (!crate::leanh::lean_is_exclusive(v___y_1344_)) as u8;
                if v_isSharedCheck_1407_ == 0 {
                    v___x_1352_ = v___y_1344_;
                    v_isShared_1353_ = v_isSharedCheck_1407_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_1350_);
                    crate::leanh::lean_inc(v_trace_1349_);
                    crate::leanh::lean_inc(v_log_1346_);
                    crate::leanh::lean_dec(v___y_1344_);
                    v___x_1352_ = crate::leanh::lean_box(0);
                    v_isShared_1353_ = v_isSharedCheck_1407_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_leanTrace_1354_ = crate::leanh::lean_ctor_get(v___y_1343_, 2);
                crate::leanh::lean_inc_ref(v_leanTrace_1354_);
                v___x_1355_ = l_Lake_BuildTrace_mix(v_trace_1349_, v_leanTrace_1354_);
                v___x_1396_ = l_Lake_Hash_nil;
                v___x_1397_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1398_ = lean_array_get_size(v_traceArgs_1336_);
                v___x_1399_ = lean_nat_dec_lt(v___x_1397_, v___x_1398_);
                if v___x_1399_ == 0 {
                    v___y_1357_ = v___x_1396_;
                    state = 2;
                    continue;
                } else {
                    v___x_1400_ = lean_nat_dec_le(v___x_1398_, v___x_1398_);
                    if v___x_1400_ == 0 {
                        if v___x_1399_ == 0 {
                            v___y_1357_ = v___x_1396_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1401_ = 0usize;
                            v___x_1402_ = lean_usize_of_nat(v___x_1398_);
                            v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_1336_, v___x_1401_, v___x_1402_, v___x_1396_);
                            v___y_1357_ = v___x_1403_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1404_ = 0usize;
                        v___x_1405_ = lean_usize_of_nat(v___x_1398_);
                        v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_1336_, v___x_1404_, v___x_1405_, v___x_1396_);
                        v___y_1357_ = v___x_1406_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1358_ = l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0;
                v___x_1359_ = l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1;
                crate::leanh::lean_inc_ref(v_traceArgs_1336_);
                v___x_1360_ = lean_array_to_list(v_traceArgs_1336_);
                v___x_1361_ =
                    l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v___x_1360_);
                crate::leanh::lean_dec(v___x_1360_);
                v___x_1362_ = lean_string_append(v___x_1359_, v___x_1361_);
                crate::leanh::lean_dec_ref(v___x_1361_);
                v___x_1363_ = lean_string_append(v___x_1358_, v___x_1362_);
                crate::leanh::lean_dec_ref(v___x_1362_);
                v___x_1364_ = l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2;
                v___x_1365_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4_once
                    ),
                    _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4,
                );
                v___x_1366_ = crate::leanh::lean_alloc_ctor(0, 3, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1366_, 0, v___x_1363_);
                crate::leanh::lean_ctor_set(v___x_1366_, 1, v___x_1364_);
                crate::leanh::lean_ctor_set(v___x_1366_, 2, v___x_1365_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1366_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___y_1357_,
                );
                v___x_1367_ = l_Lake_BuildTrace_mix(v___x_1355_, v___x_1366_);
                v___x_1368_ = l_Lake_platformTrace;
                v___x_1369_ = l_Lake_BuildTrace_mix(v___x_1367_, v___x_1368_);
                if v_isShared_1353_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1352_, 1, v___x_1369_);
                    v___x_1371_ = v___x_1352_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_log_1346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_buildTime_1350_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1395_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1347_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1395_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1348_,
                    );
                    v___x_1371_ = v_reuseFailAlloc_1395_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1372_ = l_Lake_sharedLibExt;
                crate::leanh::lean_inc_ref(v_staticLib_1338_);
                v___x_1373_ = l_System_FilePath_withExtension(v_staticLib_1338_, v___x_1372_);
                crate::leanh::lean_inc_ref_n(v___x_1373_, 2);
                v___f_1374_ = crate::leanh::lean_alloc_closure(
                    l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_1374_, 0, v_weakArgs_1337_);
                crate::leanh::lean_closure_set(v___f_1374_, 1, v_traceArgs_1336_);
                crate::leanh::lean_closure_set(v___f_1374_, 2, v___x_1373_);
                crate::leanh::lean_closure_set(v___f_1374_, 3, v_staticLib_1338_);
                v___x_1375_ = 0;
                v___x_1376_ = l_Lake_buildFileUnlessUpToDate_x27(
                    v___x_1373_,
                    v___f_1374_,
                    v___x_1375_,
                    v___y_1339_,
                    v___y_1340_,
                    v___y_1341_,
                    v___y_1342_,
                    v___y_1343_,
                    v___x_1371_,
                );
                if crate::leanh::lean_obj_tag(v___x_1376_) == 0 {
                    v_a_1377_ = crate::leanh::lean_ctor_get(v___x_1376_, 1);
                    v_isSharedCheck_1384_ = (!crate::leanh::lean_is_exclusive(v___x_1376_)) as u8;
                    if v_isSharedCheck_1384_ == 0 {
                        v_unused_1385_ = crate::leanh::lean_ctor_get(v___x_1376_, 0);
                        crate::leanh::lean_dec(v_unused_1385_);
                        v___x_1379_ = v___x_1376_;
                        v_isShared_1380_ = v_isSharedCheck_1384_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1377_);
                        crate::leanh::lean_dec(v___x_1376_);
                        v___x_1379_ = crate::leanh::lean_box(0);
                        v_isShared_1380_ = v_isSharedCheck_1384_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1373_);
                    v_a_1386_ = crate::leanh::lean_ctor_get(v___x_1376_, 0);
                    v_a_1387_ = crate::leanh::lean_ctor_get(v___x_1376_, 1);
                    v_isSharedCheck_1394_ = (!crate::leanh::lean_is_exclusive(v___x_1376_)) as u8;
                    if v_isSharedCheck_1394_ == 0 {
                        v___x_1389_ = v___x_1376_;
                        v_isShared_1390_ = v_isSharedCheck_1394_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1387_);
                        crate::leanh::lean_inc(v_a_1386_);
                        crate::leanh::lean_dec(v___x_1376_);
                        v___x_1389_ = crate::leanh::lean_box(0);
                        v_isShared_1390_ = v_isSharedCheck_1394_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1380_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1379_, 0, v___x_1373_);
                    v___x_1382_ = v___x_1379_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1383_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_a_1377_);
                    v___x_1382_ = v_reuseFailAlloc_1383_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1382_;
            }
            6 => {
                if v_isShared_1390_ == 0 {
                    v___x_1392_ = v___x_1389_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_a_1387_);
                    v___x_1392_ = v_reuseFailAlloc_1393_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1392_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(
    mut v_traceArgs_1408_: *mut crate::leanh::LeanObject,
    mut v_weakArgs_1409_: *mut crate::leanh::LeanObject,
    mut v_staticLib_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
    mut v___y_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ = l_Lake_buildLeanSharedLibOfStatic___lam__1(
        v_traceArgs_1408_,
        v_weakArgs_1409_,
        v_staticLib_1410_,
        v___y_1411_,
        v___y_1412_,
        v___y_1413_,
        v___y_1414_,
        v___y_1415_,
        v___y_1416_,
    );
    crate::leanh::lean_dec_ref(v___y_1415_);
    crate::leanh::lean_dec(v___y_1414_);
    crate::leanh::lean_dec(v___y_1413_);
    crate::leanh::lean_dec(v___y_1412_);
    return v_res_1418_;
}
pub unsafe fn l_Lake_buildLeanSharedLibOfStatic(
    mut v_staticLibJob_1419_: *mut crate::leanh::LeanObject,
    mut v_weakArgs_1420_: *mut crate::leanh::LeanObject,
    mut v_traceArgs_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
    mut v_a_1425_: *mut crate::leanh::LeanObject,
    mut v_a_1426_: *mut crate::leanh::LeanObject,
    mut v_a_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1429_ = crate::leanh::lean_alloc_closure(
        l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed as *mut core::ffi::c_void,
        10,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1429_, 0, v_traceArgs_1421_);
    crate::leanh::lean_closure_set(v___f_1429_, 1, v_weakArgs_1420_);
    v___x_1430_ = l_Lake_instDataKindFilePath;
    v___x_1431_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1432_ = 0;
    v___x_1433_ = l_Lake_Job_mapM___redArg(
        v___x_1430_,
        v_staticLibJob_1419_,
        v___f_1429_,
        v___x_1431_,
        v___x_1432_,
        v_a_1422_,
        v_a_1423_,
        v_a_1424_,
        v_a_1425_,
        v_a_1426_,
        v_a_1427_,
    );
    return v___x_1433_;
}
pub unsafe fn l_Lake_buildLeanSharedLibOfStatic___boxed(
    mut v_staticLibJob_1434_: *mut crate::leanh::LeanObject,
    mut v_weakArgs_1435_: *mut crate::leanh::LeanObject,
    mut v_traceArgs_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
    mut v_a_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
    mut v_a_1442_: *mut crate::leanh::LeanObject,
    mut v_a_1443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1444_ = l_Lake_buildLeanSharedLibOfStatic(
        v_staticLibJob_1434_,
        v_weakArgs_1435_,
        v_traceArgs_1436_,
        v_a_1437_,
        v_a_1438_,
        v_a_1439_,
        v_a_1440_,
        v_a_1441_,
        v_a_1442_,
    );
    crate::leanh::lean_dec_ref(v_a_1442_);
    crate::leanh::lean_dec_ref(v_a_1441_);
    crate::leanh::lean_dec(v_a_1440_);
    crate::leanh::lean_dec(v_a_1439_);
    crate::leanh::lean_dec(v_a_1438_);
    return v_res_1444_;
}
pub unsafe fn _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ =
        l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1;
    v___x_1449_ = l_Lake_BuildTrace_nil(v___x_1448_);
    return v___x_1449_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(
    mut v___x_1450_: *mut crate::leanh::LeanObject,
    mut v_config_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
    mut v___y_1454_: *mut crate::leanh::LeanObject,
    mut v___y_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v_moreLinkArgs_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___y_1452_);
                crate::leanh::lean_inc_ref(v___y_1456_);
                crate::leanh::lean_inc(v___y_1455_);
                crate::leanh::lean_inc(v___y_1454_);
                crate::leanh::lean_inc(v___y_1453_);
                v___x_1459_ = crate::leanh::lean_apply_7(
                    v___y_1452_,
                    v___x_1450_,
                    v___y_1453_,
                    v___y_1454_,
                    v___y_1455_,
                    v___y_1456_,
                    v___y_1457_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1459_) == 0 {
                    v_toLeanConfig_1460_ = crate::leanh::lean_ctor_get(v_config_1451_, 1);
                    crate::leanh::lean_inc_ref(v_toLeanConfig_1460_);
                    crate::leanh::lean_dec_ref(v_config_1451_);
                    v_a_1461_ = crate::leanh::lean_ctor_get(v___x_1459_, 0);
                    v_a_1462_ = crate::leanh::lean_ctor_get(v___x_1459_, 1);
                    v_isSharedCheck_1473_ = (!crate::leanh::lean_is_exclusive(v___x_1459_)) as u8;
                    if v_isSharedCheck_1473_ == 0 {
                        v___x_1464_ = v___x_1459_;
                        v_isShared_1465_ = v_isSharedCheck_1473_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1462_);
                        crate::leanh::lean_inc(v_a_1461_);
                        crate::leanh::lean_dec(v___x_1459_);
                        v___x_1464_ = crate::leanh::lean_box(0);
                        v_isShared_1465_ = v_isSharedCheck_1473_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1452_);
                    crate::leanh::lean_dec_ref(v_config_1451_);
                    return v___x_1459_;
                }
            }
            1 => {
                v_moreLinkArgs_1466_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1460_, 8);
                crate::leanh::lean_inc_ref(v_moreLinkArgs_1466_);
                crate::leanh::lean_dec_ref(v_toLeanConfig_1460_);
                v___x_1467_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0;
                v___x_1468_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once), _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
                v___x_1469_ = l_Lake_buildLeanSharedLibOfStatic(
                    v_a_1461_,
                    v_moreLinkArgs_1466_,
                    v___x_1467_,
                    v___y_1452_,
                    v___y_1453_,
                    v___y_1454_,
                    v___y_1455_,
                    v___y_1456_,
                    v___x_1468_,
                );
                if v_isShared_1465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1464_, 0, v___x_1469_);
                    v___x_1471_ = v___x_1464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1472_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_a_1462_);
                    v___x_1471_ = v_reuseFailAlloc_1472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(
    mut v___x_1474_: *mut crate::leanh::LeanObject,
    mut v_config_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1483_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(
        v___x_1474_,
        v_config_1475_,
        v___y_1476_,
        v___y_1477_,
        v___y_1478_,
        v___y_1479_,
        v___y_1480_,
        v___y_1481_,
    );
    crate::leanh::lean_dec_ref(v___y_1480_);
    crate::leanh::lean_dec(v___y_1479_);
    crate::leanh::lean_dec(v___y_1478_);
    crate::leanh::lean_dec(v___y_1477_);
    return v_res_1483_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(
    mut v_lib_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
    mut v_a_1487_: *mut crate::leanh::LeanObject,
    mut v_a_1488_: *mut crate::leanh::LeanObject,
    mut v_a_1489_: *mut crate::leanh::LeanObject,
    mut v_a_1490_: *mut crate::leanh::LeanObject,
    mut v_a_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v_task_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v_registeredJobs_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: u8 = 0;
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v_job_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_unused_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1493_ = crate::leanh::lean_ctor_get(v_lib_1485_, 0);
                v_name_1494_ = crate::leanh::lean_ctor_get(v_lib_1485_, 1);
                crate::leanh::lean_inc_n(v_name_1494_, 2);
                v_keyName_1495_ = crate::leanh::lean_ctor_get(v_pkg_1493_, 2);
                v_config_1496_ = crate::leanh::lean_ctor_get(v_pkg_1493_, 6);
                crate::leanh::lean_inc_ref(v_config_1496_);
                v___x_1497_ = l_Lake_instDataKindFilePath;
                v___x_1498_ = l_Lake_ExternLib_staticFacet;
                crate::leanh::lean_inc(v_keyName_1495_);
                v___x_1499_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1499_, 0, v_keyName_1495_);
                crate::leanh::lean_ctor_set(v___x_1499_, 1, v_name_1494_);
                v___x_1500_ = l_Lake_ExternLib_keyword;
                v___x_1501_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1499_);
                crate::leanh::lean_ctor_set(v___x_1501_, 1, v___x_1500_);
                crate::leanh::lean_ctor_set(v___x_1501_, 2, v_lib_1485_);
                crate::leanh::lean_ctor_set(v___x_1501_, 3, v___x_1498_);
                v___f_1502_ = crate::leanh::lean_alloc_closure(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___f_1502_, 0, v___x_1501_);
                crate::leanh::lean_closure_set(v___f_1502_, 1, v_config_1496_);
                v___x_1503_ = l_Lake_ensureJob___redArg(
                    v___x_1497_,
                    v___f_1502_,
                    v_a_1486_,
                    v_a_1487_,
                    v_a_1488_,
                    v_a_1489_,
                    v_a_1490_,
                    v_a_1491_,
                );
                if crate::leanh::lean_obj_tag(v___x_1503_) == 0 {
                    v_a_1504_ = crate::leanh::lean_ctor_get(v___x_1503_, 0);
                    v_a_1505_ = crate::leanh::lean_ctor_get(v___x_1503_, 1);
                    v_isSharedCheck_1535_ = (!crate::leanh::lean_is_exclusive(v___x_1503_)) as u8;
                    if v_isSharedCheck_1535_ == 0 {
                        v___x_1507_ = v___x_1503_;
                        v_isShared_1508_ = v_isSharedCheck_1535_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1505_);
                        crate::leanh::lean_inc(v_a_1504_);
                        crate::leanh::lean_dec(v___x_1503_);
                        v___x_1507_ = crate::leanh::lean_box(0);
                        v_isShared_1508_ = v_isSharedCheck_1535_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_1494_);
                    return v___x_1503_;
                }
            }
            1 => {
                v_task_1509_ = crate::leanh::lean_ctor_get(v_a_1504_, 0);
                v_kind_1510_ = crate::leanh::lean_ctor_get(v_a_1504_, 1);
                v_isSharedCheck_1533_ = (!crate::leanh::lean_is_exclusive(v_a_1504_)) as u8;
                if v_isSharedCheck_1533_ == 0 {
                    v_unused_1534_ = crate::leanh::lean_ctor_get(v_a_1504_, 2);
                    crate::leanh::lean_dec(v_unused_1534_);
                    v___x_1512_ = v_a_1504_;
                    v_isShared_1513_ = v_isSharedCheck_1533_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_1510_);
                    crate::leanh::lean_inc(v_task_1509_);
                    crate::leanh::lean_dec(v_a_1504_);
                    v___x_1512_ = crate::leanh::lean_box(0);
                    v_isShared_1513_ = v_isSharedCheck_1533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_1514_ = crate::leanh::lean_ctor_get(v_a_1490_, 3);
                v___x_1515_ = lean_st_ref_take(v_registeredJobs_1514_);
                v___x_1516_ =
                    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
                v___x_1517_ = l_Lean_Name_str___override(v_name_1494_, v___x_1516_);
                v___x_1518_ = 1;
                v___x_1519_ = l_Lean_Name_toString(v___x_1517_, v___x_1518_);
                v___x_1520_ =
                    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0;
                v___x_1521_ = lean_string_append(v___x_1519_, v___x_1520_);
                v___x_1522_ = 0;
                if v_isShared_1513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1512_, 2, v___x_1521_);
                    v_job_1524_ = v___x_1512_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1532_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_task_1509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_kind_1510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 2, v___x_1521_);
                    v_job_1524_ = v_reuseFailAlloc_1532_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_1524_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1522_,
                );
                crate::leanh::lean_inc_ref(v_job_1524_);
                v___x_1525_ = l_Lake_Job_toOpaque___redArg(v_job_1524_);
                v___x_1526_ = lean_array_push(v___x_1515_, v___x_1525_);
                v___x_1527_ = lean_st_ref_set(v_registeredJobs_1514_, v___x_1526_);
                v___x_1528_ = l_Lake_Job_renew___redArg(v_job_1524_);
                if v_isShared_1508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1528_);
                    v___x_1530_ = v___x_1507_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_a_1505_);
                    v___x_1530_ = v_reuseFailAlloc_1531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(
    mut v_lib_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
    mut v_a_1538_: *mut crate::leanh::LeanObject,
    mut v_a_1539_: *mut crate::leanh::LeanObject,
    mut v_a_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
    mut v_a_1542_: *mut crate::leanh::LeanObject,
    mut v_a_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1544_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(
        v_lib_1536_,
        v_a_1537_,
        v_a_1538_,
        v_a_1539_,
        v_a_1540_,
        v_a_1541_,
        v_a_1542_,
    );
    crate::leanh::lean_dec_ref(v_a_1541_);
    crate::leanh::lean_dec(v_a_1540_);
    crate::leanh::lean_dec(v_a_1539_);
    crate::leanh::lean_dec(v_a_1538_);
    return v_res_1544_;
}
pub unsafe fn _init_l_Lake_ExternLib_sharedFacetConfig___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___f_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: u8 = 0;
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1546_ = l_Lake_ExternLib_staticFacetConfig___closed__0;
    v___x_1547_ = 1;
    v___x_1548_ = l_Lake_instDataKindFilePath;
    v___x_1549_ = l_Lake_ExternLib_sharedFacetConfig___closed__0;
    v___x_1550_ = l_Lake_ExternLib_keyword;
    v___x_1551_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1551_, 0, v___x_1550_);
    crate::leanh::lean_ctor_set(v___x_1551_, 1, v___x_1549_);
    crate::leanh::lean_ctor_set(v___x_1551_, 2, v___x_1548_);
    crate::leanh::lean_ctor_set(v___x_1551_, 3, v___f_1546_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1551_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_1547_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1551_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v___x_1547_,
    );
    return v___x_1551_;
}
pub unsafe fn _init_l_Lake_ExternLib_sharedFacetConfig() -> *mut crate::leanh::LeanObject {
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ExternLib_sharedFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_ExternLib_sharedFacetConfig___closed__1_once),
        _init_l_Lake_ExternLib_sharedFacetConfig___closed__1,
    );
    return v___x_1552_;
}
pub unsafe fn _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ =
        l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3;
    v___x_1559_ = lean_string_utf8_byte_size(v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(
    mut v_sharedLib_1561_: *mut crate::leanh::LeanObject,
    mut v___y_1562_: *mut crate::leanh::LeanObject,
    mut v___y_1563_: *mut crate::leanh::LeanObject,
    mut v___y_1564_: *mut crate::leanh::LeanObject,
    mut v___y_1565_: *mut crate::leanh::LeanObject,
    mut v___y_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___y_1573_: u8 = 0;
    let mut v_log_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1575_: u8 = 0;
    let mut v_wantsRebuild_1576_: u8 = 0;
    let mut v_trace_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1581_: u8 = 0;
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: u8 = 0;
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1615_: u8 = 0;
    let mut v_wantsRebuild_1616_: u8 = 0;
    let mut v_trace_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_sharedLib_1561_);
                v___x_1569_ = l_System_FilePath_fileStem(v_sharedLib_1561_);
                if crate::leanh::lean_obj_tag(v___x_1569_) == 1 {
                    v_val_1570_ = crate::leanh::lean_ctor_get(v___x_1569_, 0);
                    crate::leanh::lean_inc(v_val_1570_);
                    crate::leanh::lean_dec_ref_known(v___x_1569_, 1);
                    v___x_1571_ = l_System_Platform_isWindows;
                    if v___x_1571_ == 0 {
                        v___x_1604_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3;
                        v___x_1605_ = lean_string_utf8_byte_size(v_val_1570_);
                        v___x_1606_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_once), _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4);
                        v___x_1607_ = lean_nat_dec_le(v___x_1606_, v___x_1605_);
                        if v___x_1607_ == 0 {
                            v___y_1573_ = v___x_1571_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1608_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1609_ = lean_string_memcmp(
                                v_val_1570_,
                                v___x_1604_,
                                v___x_1608_,
                                v___x_1608_,
                                v___x_1606_,
                            );
                            v___y_1573_ = v___x_1609_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1610_ = 0;
                        v___x_1611_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2;
                        v___x_1612_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1612_, 0, v_sharedLib_1561_);
                        crate::leanh::lean_ctor_set(v___x_1612_, 1, v_val_1570_);
                        crate::leanh::lean_ctor_set(v___x_1612_, 2, v___x_1611_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1612_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v___x_1610_,
                        );
                        v___x_1613_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1613_, 0, v___x_1612_);
                        crate::leanh::lean_ctor_set(v___x_1613_, 1, v___y_1567_);
                        return v___x_1613_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1569_);
                    v_log_1614_ = crate::leanh::lean_ctor_get(v___y_1567_, 0);
                    v_action_1615_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1567_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_1616_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1567_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_1617_ = crate::leanh::lean_ctor_get(v___y_1567_, 1);
                    v_buildTime_1618_ = crate::leanh::lean_ctor_get(v___y_1567_, 2);
                    v_isSharedCheck_1634_ = (!crate::leanh::lean_is_exclusive(v___y_1567_)) as u8;
                    if v_isSharedCheck_1634_ == 0 {
                        v___x_1620_ = v___y_1567_;
                        v_isShared_1621_ = v_isSharedCheck_1634_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_buildTime_1618_);
                        crate::leanh::lean_inc(v_trace_1617_);
                        crate::leanh::lean_inc(v_log_1614_);
                        crate::leanh::lean_dec(v___y_1567_);
                        v___x_1620_ = crate::leanh::lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1634_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1573_ == 0 {
                    crate::leanh::lean_dec(v_val_1570_);
                    v_log_1574_ = crate::leanh::lean_ctor_get(v___y_1567_, 0);
                    v_action_1575_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1567_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_1576_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1567_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_1577_ = crate::leanh::lean_ctor_get(v___y_1567_, 1);
                    v_buildTime_1578_ = crate::leanh::lean_ctor_get(v___y_1567_, 2);
                    v_isSharedCheck_1594_ = (!crate::leanh::lean_is_exclusive(v___y_1567_)) as u8;
                    if v_isSharedCheck_1594_ == 0 {
                        v___x_1580_ = v___y_1567_;
                        v_isShared_1581_ = v_isSharedCheck_1594_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_buildTime_1578_);
                        crate::leanh::lean_inc(v_trace_1577_);
                        crate::leanh::lean_inc(v_log_1574_);
                        crate::leanh::lean_dec(v___y_1567_);
                        v___x_1580_ = crate::leanh::lean_box(0);
                        v_isShared_1581_ = v_isSharedCheck_1594_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1595_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1596_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1597_ = lean_string_utf8_byte_size(v_val_1570_);
                    crate::leanh::lean_inc(v_val_1570_);
                    v___x_1598_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1598_, 0, v_val_1570_);
                    crate::leanh::lean_ctor_set(v___x_1598_, 1, v___x_1596_);
                    crate::leanh::lean_ctor_set(v___x_1598_, 2, v___x_1597_);
                    v___x_1599_ = l_String_Slice_Pos_nextn(v___x_1598_, v___x_1596_, v___x_1595_);
                    crate::leanh::lean_dec_ref_known(v___x_1598_, 3);
                    v___x_1600_ = lean_string_utf8_extract(v_val_1570_, v___x_1599_, v___x_1597_);
                    crate::leanh::lean_dec(v___x_1599_);
                    crate::leanh::lean_dec(v_val_1570_);
                    v___x_1601_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2;
                    v___x_1602_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1602_, 0, v_sharedLib_1561_);
                    crate::leanh::lean_ctor_set(v___x_1602_, 1, v___x_1600_);
                    crate::leanh::lean_ctor_set(v___x_1602_, 2, v___x_1601_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1602_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_1571_,
                    );
                    v___x_1603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1603_, 0, v___x_1602_);
                    crate::leanh::lean_ctor_set(v___x_1603_, 1, v___y_1567_);
                    return v___x_1603_;
                }
            }
            2 => {
                v___x_1582_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0;
                v___x_1583_ = lean_string_append(v___x_1582_, v_sharedLib_1561_);
                crate::leanh::lean_dec_ref(v_sharedLib_1561_);
                v___x_1584_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1;
                v___x_1585_ = lean_string_append(v___x_1583_, v___x_1584_);
                v___x_1586_ = 3;
                v___x_1587_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1587_, 0, v___x_1585_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1586_,
                );
                v___x_1588_ = lean_array_get_size(v_log_1574_);
                v___x_1589_ = lean_array_push(v_log_1574_, v___x_1587_);
                if v_isShared_1581_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1580_, 0, v___x_1589_);
                    v___x_1591_ = v___x_1580_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_trace_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_buildTime_1578_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1593_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1575_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1593_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1576_,
                    );
                    v___x_1591_ = v_reuseFailAlloc_1593_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1592_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1592_, 0, v___x_1588_);
                crate::leanh::lean_ctor_set(v___x_1592_, 1, v___x_1591_);
                return v___x_1592_;
            }
            4 => {
                v___x_1622_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0;
                v___x_1623_ = lean_string_append(v___x_1622_, v_sharedLib_1561_);
                crate::leanh::lean_dec_ref(v_sharedLib_1561_);
                v___x_1624_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5;
                v___x_1625_ = lean_string_append(v___x_1623_, v___x_1624_);
                v___x_1626_ = 3;
                v___x_1627_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1627_, 0, v___x_1625_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1626_,
                );
                v___x_1628_ = lean_array_get_size(v_log_1614_);
                v___x_1629_ = lean_array_push(v_log_1614_, v___x_1627_);
                if v_isShared_1621_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1629_);
                    v___x_1631_ = v___x_1620_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1633_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_trace_1617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_buildTime_1618_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1633_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1615_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1633_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1616_,
                    );
                    v___x_1631_ = v_reuseFailAlloc_1633_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1632_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1632_, 0, v___x_1628_);
                crate::leanh::lean_ctor_set(v___x_1632_, 1, v___x_1631_);
                return v___x_1632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(
    mut v_sharedLib_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1643_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(
        v_sharedLib_1635_,
        v___y_1636_,
        v___y_1637_,
        v___y_1638_,
        v___y_1639_,
        v___y_1640_,
        v___y_1641_,
    );
    crate::leanh::lean_dec_ref(v___y_1640_);
    crate::leanh::lean_dec(v___y_1639_);
    crate::leanh::lean_dec(v___y_1638_);
    crate::leanh::lean_dec(v___y_1637_);
    crate::leanh::lean_dec_ref(v___y_1636_);
    return v_res_1643_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(
    mut v_sharedLibTarget_1645_: *mut crate::leanh::LeanObject,
    mut v_a_1646_: *mut crate::leanh::LeanObject,
    mut v_a_1647_: *mut crate::leanh::LeanObject,
    mut v_a_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1653_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0;
    v___x_1654_ = l_Lake_instDataKindDynlib;
    v___x_1655_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1656_ = 0;
    v___x_1657_ = l_Lake_Job_mapM___redArg(
        v___x_1654_,
        v_sharedLibTarget_1645_,
        v___f_1653_,
        v___x_1655_,
        v___x_1656_,
        v_a_1646_,
        v_a_1647_,
        v_a_1648_,
        v_a_1649_,
        v_a_1650_,
        v_a_1651_,
    );
    return v___x_1657_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(
    mut v_sharedLibTarget_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
    mut v_a_1660_: *mut crate::leanh::LeanObject,
    mut v_a_1661_: *mut crate::leanh::LeanObject,
    mut v_a_1662_: *mut crate::leanh::LeanObject,
    mut v_a_1663_: *mut crate::leanh::LeanObject,
    mut v_a_1664_: *mut crate::leanh::LeanObject,
    mut v_a_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(
        v_sharedLibTarget_1658_,
        v_a_1659_,
        v_a_1660_,
        v_a_1661_,
        v_a_1662_,
        v_a_1663_,
        v_a_1664_,
    );
    crate::leanh::lean_dec_ref(v_a_1664_);
    crate::leanh::lean_dec_ref(v_a_1663_);
    crate::leanh::lean_dec(v_a_1662_);
    crate::leanh::lean_dec(v_a_1661_);
    crate::leanh::lean_dec(v_a_1660_);
    return v_res_1666_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(
    mut v___x_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut v_a_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___y_1668_);
                crate::leanh::lean_inc_ref(v___y_1672_);
                crate::leanh::lean_inc(v___y_1671_);
                crate::leanh::lean_inc(v___y_1670_);
                crate::leanh::lean_inc(v___y_1669_);
                v___x_1675_ = crate::leanh::lean_apply_7(
                    v___y_1668_,
                    v___x_1667_,
                    v___y_1669_,
                    v___y_1670_,
                    v___y_1671_,
                    v___y_1672_,
                    v___y_1673_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1675_) == 0 {
                    v_a_1676_ = crate::leanh::lean_ctor_get(v___x_1675_, 0);
                    v_a_1677_ = crate::leanh::lean_ctor_get(v___x_1675_, 1);
                    v_isSharedCheck_1686_ = (!crate::leanh::lean_is_exclusive(v___x_1675_)) as u8;
                    if v_isSharedCheck_1686_ == 0 {
                        v___x_1679_ = v___x_1675_;
                        v_isShared_1680_ = v_isSharedCheck_1686_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1677_);
                        crate::leanh::lean_inc(v_a_1676_);
                        crate::leanh::lean_dec(v___x_1675_);
                        v___x_1679_ = crate::leanh::lean_box(0);
                        v_isShared_1680_ = v_isSharedCheck_1686_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1668_);
                    v_a_1687_ = crate::leanh::lean_ctor_get(v___x_1675_, 0);
                    v_a_1688_ = crate::leanh::lean_ctor_get(v___x_1675_, 1);
                    v_isSharedCheck_1695_ = (!crate::leanh::lean_is_exclusive(v___x_1675_)) as u8;
                    if v_isSharedCheck_1695_ == 0 {
                        v___x_1690_ = v___x_1675_;
                        v_isShared_1691_ = v_isSharedCheck_1695_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1688_);
                        crate::leanh::lean_inc(v_a_1687_);
                        crate::leanh::lean_dec(v___x_1675_);
                        v___x_1690_ = crate::leanh::lean_box(0);
                        v_isShared_1691_ = v_isSharedCheck_1695_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1681_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once), _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
                v___x_1682_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(
                    v_a_1676_,
                    v___y_1668_,
                    v___y_1669_,
                    v___y_1670_,
                    v___y_1671_,
                    v___y_1672_,
                    v___x_1681_,
                );
                if v_isShared_1680_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1682_);
                    v___x_1684_ = v___x_1679_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_a_1677_);
                    v___x_1684_ = v_reuseFailAlloc_1685_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1684_;
            }
            3 => {
                if v_isShared_1691_ == 0 {
                    v___x_1693_ = v___x_1690_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1694_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_a_1688_);
                    v___x_1693_ = v_reuseFailAlloc_1694_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(
    mut v___x_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(
        v___x_1696_,
        v___y_1697_,
        v___y_1698_,
        v___y_1699_,
        v___y_1700_,
        v___y_1701_,
        v___y_1702_,
    );
    crate::leanh::lean_dec_ref(v___y_1701_);
    crate::leanh::lean_dec(v___y_1700_);
    crate::leanh::lean_dec(v___y_1699_);
    crate::leanh::lean_dec(v___y_1698_);
    return v_res_1704_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(
    mut v_lib_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
    mut v_a_1710_: *mut crate::leanh::LeanObject,
    mut v_a_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1728_: u8 = 0;
    let mut v_task_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1733_: u8 = 0;
    let mut v_registeredJobs_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    let mut v_job_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut v_unused_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1714_ = crate::leanh::lean_ctor_get(v_lib_1706_, 0);
                v_name_1715_ = crate::leanh::lean_ctor_get(v_lib_1706_, 1);
                crate::leanh::lean_inc_n(v_name_1715_, 2);
                v_keyName_1716_ = crate::leanh::lean_ctor_get(v_pkg_1714_, 2);
                v___x_1717_ = l_Lake_instDataKindDynlib;
                v___x_1718_ = l_Lake_ExternLib_sharedFacet;
                crate::leanh::lean_inc(v_keyName_1716_);
                v___x_1719_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1719_, 0, v_keyName_1716_);
                crate::leanh::lean_ctor_set(v___x_1719_, 1, v_name_1715_);
                v___x_1720_ = l_Lake_ExternLib_keyword;
                v___x_1721_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1721_, 0, v___x_1719_);
                crate::leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                crate::leanh::lean_ctor_set(v___x_1721_, 2, v_lib_1706_);
                crate::leanh::lean_ctor_set(v___x_1721_, 3, v___x_1718_);
                v___f_1722_ = crate::leanh::lean_alloc_closure(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1722_, 0, v___x_1721_);
                v___x_1723_ = l_Lake_ensureJob___redArg(
                    v___x_1717_,
                    v___f_1722_,
                    v_a_1707_,
                    v_a_1708_,
                    v_a_1709_,
                    v_a_1710_,
                    v_a_1711_,
                    v_a_1712_,
                );
                if crate::leanh::lean_obj_tag(v___x_1723_) == 0 {
                    v_a_1724_ = crate::leanh::lean_ctor_get(v___x_1723_, 0);
                    v_a_1725_ = crate::leanh::lean_ctor_get(v___x_1723_, 1);
                    v_isSharedCheck_1755_ = (!crate::leanh::lean_is_exclusive(v___x_1723_)) as u8;
                    if v_isSharedCheck_1755_ == 0 {
                        v___x_1727_ = v___x_1723_;
                        v_isShared_1728_ = v_isSharedCheck_1755_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1725_);
                        crate::leanh::lean_inc(v_a_1724_);
                        crate::leanh::lean_dec(v___x_1723_);
                        v___x_1727_ = crate::leanh::lean_box(0);
                        v_isShared_1728_ = v_isSharedCheck_1755_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_1715_);
                    return v___x_1723_;
                }
            }
            1 => {
                v_task_1729_ = crate::leanh::lean_ctor_get(v_a_1724_, 0);
                v_kind_1730_ = crate::leanh::lean_ctor_get(v_a_1724_, 1);
                v_isSharedCheck_1753_ = (!crate::leanh::lean_is_exclusive(v_a_1724_)) as u8;
                if v_isSharedCheck_1753_ == 0 {
                    v_unused_1754_ = crate::leanh::lean_ctor_get(v_a_1724_, 2);
                    crate::leanh::lean_dec(v_unused_1754_);
                    v___x_1732_ = v_a_1724_;
                    v_isShared_1733_ = v_isSharedCheck_1753_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_1730_);
                    crate::leanh::lean_inc(v_task_1729_);
                    crate::leanh::lean_dec(v_a_1724_);
                    v___x_1732_ = crate::leanh::lean_box(0);
                    v_isShared_1733_ = v_isSharedCheck_1753_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_registeredJobs_1734_ = crate::leanh::lean_ctor_get(v_a_1711_, 3);
                v___x_1735_ = lean_st_ref_take(v_registeredJobs_1734_);
                v___x_1736_ =
                    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0;
                v___x_1737_ = l_Lean_Name_str___override(v_name_1715_, v___x_1736_);
                v___x_1738_ = 1;
                v___x_1739_ = l_Lean_Name_toString(v___x_1737_, v___x_1738_);
                v___x_1740_ =
                    l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0;
                v___x_1741_ = lean_string_append(v___x_1739_, v___x_1740_);
                v___x_1742_ = 0;
                if v_isShared_1733_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1732_, 2, v___x_1741_);
                    v_job_1744_ = v___x_1732_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1752_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_task_1729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_kind_1730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1752_, 2, v___x_1741_);
                    v_job_1744_ = v_reuseFailAlloc_1752_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_job_1744_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1742_,
                );
                crate::leanh::lean_inc_ref(v_job_1744_);
                v___x_1745_ = l_Lake_Job_toOpaque___redArg(v_job_1744_);
                v___x_1746_ = lean_array_push(v___x_1735_, v___x_1745_);
                v___x_1747_ = lean_st_ref_set(v_registeredJobs_1734_, v___x_1746_);
                v___x_1748_ = l_Lake_Job_renew___redArg(v_job_1744_);
                if v_isShared_1728_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1727_, 0, v___x_1748_);
                    v___x_1750_ = v___x_1727_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_a_1725_);
                    v___x_1750_ = v_reuseFailAlloc_1751_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(
    mut v_lib_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1764_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(
        v_lib_1756_,
        v_a_1757_,
        v_a_1758_,
        v_a_1759_,
        v_a_1760_,
        v_a_1761_,
        v_a_1762_,
    );
    crate::leanh::lean_dec_ref(v_a_1761_);
    crate::leanh::lean_dec(v_a_1760_);
    crate::leanh::lean_dec(v_a_1759_);
    crate::leanh::lean_dec(v_a_1758_);
    return v_res_1764_;
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(
    mut v_fmt_1765_: u8,
    mut v_a_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_fmt_1765_ == 0 {
        let mut v_path_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_path_1767_ = crate::leanh::lean_ctor_get(v_a_1766_, 0);
        crate::leanh::lean_inc_ref(v_path_1767_);
        return v_path_1767_;
    } else {
        let mut v_path_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_path_1768_ = crate::leanh::lean_ctor_get(v_a_1766_, 0);
        crate::leanh::lean_inc_ref(v_path_1768_);
        v___x_1769_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1769_, 0, v_path_1768_);
        v___x_1770_ = l_Lean_Json_compress(v___x_1769_);
        return v___x_1770_;
    }
}
pub unsafe fn l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(
    mut v_fmt_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fmt_boxed_1773_: u8 = 0;
    let mut v_res_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fmt_boxed_1773_ = (crate::leanh::lean_unbox(v_fmt_1771_) as u8);
    v_res_1774_ = l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(
        v_fmt_boxed_1773_,
        v_a_1772_,
    );
    crate::leanh::lean_dec_ref(v_a_1772_);
    return v_res_1774_;
}
pub unsafe fn _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___f_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: u8 = 0;
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1777_ = l_Lake_ExternLib_dynlibFacetConfig___closed__0;
    v___x_1778_ = 1;
    v___x_1779_ = l_Lake_instDataKindDynlib;
    v___x_1780_ = l_Lake_ExternLib_dynlibFacetConfig___closed__1;
    v___x_1781_ = l_Lake_ExternLib_keyword;
    v___x_1782_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1782_, 0, v___x_1781_);
    crate::leanh::lean_ctor_set(v___x_1782_, 1, v___x_1780_);
    crate::leanh::lean_ctor_set(v___x_1782_, 2, v___x_1779_);
    crate::leanh::lean_ctor_set(v___x_1782_, 3, v___f_1777_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1782_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_1778_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1782_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v___x_1778_,
    );
    return v___x_1782_;
}
pub unsafe fn _init_l_Lake_ExternLib_dynlibFacetConfig() -> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ExternLib_dynlibFacetConfig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_ExternLib_dynlibFacetConfig___closed__2_once),
        _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2,
    );
    return v___x_1783_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(
    mut v_lib_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
    mut v_a_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1792_ = crate::leanh::lean_ctor_get(v_lib_1784_, 0);
    v_name_1793_ = crate::leanh::lean_ctor_get(v_lib_1784_, 1);
    v_keyName_1794_ = crate::leanh::lean_ctor_get(v_pkg_1792_, 2);
    v___x_1795_ = l_Lake_ExternLib_staticFacet;
    crate::leanh::lean_inc(v_name_1793_);
    crate::leanh::lean_inc(v_keyName_1794_);
    v___x_1796_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1796_, 0, v_keyName_1794_);
    crate::leanh::lean_ctor_set(v___x_1796_, 1, v_name_1793_);
    v___x_1797_ = l_Lake_ExternLib_keyword;
    v___x_1798_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1798_, 0, v___x_1796_);
    crate::leanh::lean_ctor_set(v___x_1798_, 1, v___x_1797_);
    crate::leanh::lean_ctor_set(v___x_1798_, 2, v_lib_1784_);
    crate::leanh::lean_ctor_set(v___x_1798_, 3, v___x_1795_);
    crate::leanh::lean_inc_ref(v_a_1789_);
    crate::leanh::lean_inc(v_a_1788_);
    crate::leanh::lean_inc(v_a_1787_);
    crate::leanh::lean_inc(v_a_1786_);
    v___x_1799_ = crate::leanh::lean_apply_7(
        v_a_1785_,
        v___x_1798_,
        v_a_1786_,
        v_a_1787_,
        v_a_1788_,
        v_a_1789_,
        v_a_1790_,
        crate::leanh::lean_box(0),
    );
    return v___x_1799_;
}
pub unsafe fn l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(
    mut v_lib_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
    mut v_a_1802_: *mut crate::leanh::LeanObject,
    mut v_a_1803_: *mut crate::leanh::LeanObject,
    mut v_a_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1808_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(
        v_lib_1800_,
        v_a_1801_,
        v_a_1802_,
        v_a_1803_,
        v_a_1804_,
        v_a_1805_,
        v_a_1806_,
    );
    crate::leanh::lean_dec_ref(v_a_1805_);
    crate::leanh::lean_dec(v_a_1804_);
    crate::leanh::lean_dec(v_a_1803_);
    crate::leanh::lean_dec(v_a_1802_);
    return v_res_1808_;
}
pub unsafe fn _init_l_Lake_ExternLib_defaultFacetConfig___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: u8 = 0;
    let mut v___f_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = 0;
    v___f_1811_ = l_Lake_ExternLib_staticFacetConfig___closed__0;
    v___x_1812_ = 1;
    v___x_1813_ = l_Lake_instDataKindFilePath;
    v___x_1814_ = l_Lake_ExternLib_defaultFacetConfig___closed__0;
    v___x_1815_ = l_Lake_ExternLib_keyword;
    v___x_1816_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1815_);
    crate::leanh::lean_ctor_set(v___x_1816_, 1, v___x_1814_);
    crate::leanh::lean_ctor_set(v___x_1816_, 2, v___x_1813_);
    crate::leanh::lean_ctor_set(v___x_1816_, 3, v___f_1811_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1816_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_1812_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1816_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v___x_1810_,
    );
    return v___x_1816_;
}
pub unsafe fn _init_l_Lake_ExternLib_defaultFacetConfig() -> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ExternLib_defaultFacetConfig___closed__1),
        core::ptr::addr_of_mut!(l_Lake_ExternLib_defaultFacetConfig___closed__1_once),
        _init_l_Lake_ExternLib_defaultFacetConfig___closed__1,
    );
    return v___x_1817_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(
    mut v_k_1818_: *mut crate::leanh::LeanObject,
    mut v_v_1819_: *mut crate::leanh::LeanObject,
    mut v_t_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1829_: u8 = 0;
    let mut v_impl_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v_size_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1860_: u8 = 0;
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_unused_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_unused_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_unused_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v_unused_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1939_: u8 = 0;
    let mut v_k_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v_unused_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_unused_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1988_: u8 = 0;
    let mut v_size_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2000_: u8 = 0;
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_unused_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut v_unused_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_unused_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2061_: u8 = 0;
    let mut v_k_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_unused_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut v_unused_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2097_: u8 = 0;
    let mut v_unused_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1820_) == 0 {
                    v_size_1821_ = crate::leanh::lean_ctor_get(v_t_1820_, 0);
                    v_k_1822_ = crate::leanh::lean_ctor_get(v_t_1820_, 1);
                    v_v_1823_ = crate::leanh::lean_ctor_get(v_t_1820_, 2);
                    v_l_1824_ = crate::leanh::lean_ctor_get(v_t_1820_, 3);
                    v_r_1825_ = crate::leanh::lean_ctor_get(v_t_1820_, 4);
                    v_isSharedCheck_2105_ = (!crate::leanh::lean_is_exclusive(v_t_1820_)) as u8;
                    if v_isSharedCheck_2105_ == 0 {
                        v___x_1827_ = v_t_1820_;
                        v_isShared_1828_ = v_isSharedCheck_2105_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1825_);
                        crate::leanh::lean_inc(v_l_1824_);
                        crate::leanh::lean_inc(v_v_1823_);
                        crate::leanh::lean_inc(v_k_1822_);
                        crate::leanh::lean_inc(v_size_1821_);
                        crate::leanh::lean_dec(v_t_1820_);
                        v___x_1827_ = crate::leanh::lean_box(0);
                        v_isShared_1828_ = v_isSharedCheck_2105_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2106_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2107_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2107_, 0, v___x_2106_);
                    crate::leanh::lean_ctor_set(v___x_2107_, 1, v_k_1818_);
                    crate::leanh::lean_ctor_set(v___x_2107_, 2, v_v_1819_);
                    crate::leanh::lean_ctor_set(v___x_2107_, 3, v_t_1820_);
                    crate::leanh::lean_ctor_set(v___x_2107_, 4, v_t_1820_);
                    return v___x_2107_;
                }
            }
            1 => {
                v___x_1829_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1818_, v_k_1822_);
                match v___x_1829_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_1821_);
                        v_impl_1830_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_1818_, v_v_1819_, v_l_1824_);
                        v___x_1831_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_1825_) == 0 {
                            v_size_1832_ = crate::leanh::lean_ctor_get(v_r_1825_, 0);
                            v_size_1833_ = crate::leanh::lean_ctor_get(v_impl_1830_, 0);
                            crate::leanh::lean_inc(v_size_1833_);
                            v_k_1834_ = crate::leanh::lean_ctor_get(v_impl_1830_, 1);
                            crate::leanh::lean_inc(v_k_1834_);
                            v_v_1835_ = crate::leanh::lean_ctor_get(v_impl_1830_, 2);
                            crate::leanh::lean_inc(v_v_1835_);
                            v_l_1836_ = crate::leanh::lean_ctor_get(v_impl_1830_, 3);
                            crate::leanh::lean_inc(v_l_1836_);
                            v_r_1837_ = crate::leanh::lean_ctor_get(v_impl_1830_, 4);
                            crate::leanh::lean_inc(v_r_1837_);
                            v___x_1838_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1839_ = lean_nat_mul(v___x_1838_, v_size_1832_);
                            v___x_1840_ = lean_nat_dec_lt(v___x_1839_, v_size_1833_);
                            crate::leanh::lean_dec(v___x_1839_);
                            if v___x_1840_ == 0 {
                                crate::leanh::lean_dec(v_r_1837_);
                                crate::leanh::lean_dec(v_l_1836_);
                                crate::leanh::lean_dec(v_v_1835_);
                                crate::leanh::lean_dec(v_k_1834_);
                                v___x_1841_ = lean_nat_add(v___x_1831_, v_size_1833_);
                                crate::leanh::lean_dec(v_size_1833_);
                                v___x_1842_ = lean_nat_add(v___x_1841_, v_size_1832_);
                                crate::leanh::lean_dec(v___x_1841_);
                                if v_isShared_1828_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1827_, 3, v_impl_1830_);
                                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1842_);
                                    v___x_1844_ = v___x_1827_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1845_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1845_,
                                        0,
                                        v___x_1842_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1845_,
                                        1,
                                        v_k_1822_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1845_,
                                        2,
                                        v_v_1823_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1845_,
                                        3,
                                        v_impl_1830_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1845_,
                                        4,
                                        v_r_1825_,
                                    );
                                    v___x_1844_ = v_reuseFailAlloc_1845_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1911_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1830_)) as u8;
                                if v_isSharedCheck_1911_ == 0 {
                                    v_unused_1912_ = crate::leanh::lean_ctor_get(v_impl_1830_, 4);
                                    crate::leanh::lean_dec(v_unused_1912_);
                                    v_unused_1913_ = crate::leanh::lean_ctor_get(v_impl_1830_, 3);
                                    crate::leanh::lean_dec(v_unused_1913_);
                                    v_unused_1914_ = crate::leanh::lean_ctor_get(v_impl_1830_, 2);
                                    crate::leanh::lean_dec(v_unused_1914_);
                                    v_unused_1915_ = crate::leanh::lean_ctor_get(v_impl_1830_, 1);
                                    crate::leanh::lean_dec(v_unused_1915_);
                                    v_unused_1916_ = crate::leanh::lean_ctor_get(v_impl_1830_, 0);
                                    crate::leanh::lean_dec(v_unused_1916_);
                                    v___x_1847_ = v_impl_1830_;
                                    v_isShared_1848_ = v_isSharedCheck_1911_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1830_);
                                    v___x_1847_ = crate::leanh::lean_box(0);
                                    v_isShared_1848_ = v_isSharedCheck_1911_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1917_ = crate::leanh::lean_ctor_get(v_impl_1830_, 3);
                            crate::leanh::lean_inc(v_l_1917_);
                            if crate::leanh::lean_obj_tag(v_l_1917_) == 0 {
                                v_r_1918_ = crate::leanh::lean_ctor_get(v_impl_1830_, 4);
                                v_k_1919_ = crate::leanh::lean_ctor_get(v_impl_1830_, 1);
                                v_v_1920_ = crate::leanh::lean_ctor_get(v_impl_1830_, 2);
                                v_isSharedCheck_1931_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1830_)) as u8;
                                if v_isSharedCheck_1931_ == 0 {
                                    v_unused_1932_ = crate::leanh::lean_ctor_get(v_impl_1830_, 3);
                                    crate::leanh::lean_dec(v_unused_1932_);
                                    v_unused_1933_ = crate::leanh::lean_ctor_get(v_impl_1830_, 0);
                                    crate::leanh::lean_dec(v_unused_1933_);
                                    v___x_1922_ = v_impl_1830_;
                                    v_isShared_1923_ = v_isSharedCheck_1931_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1918_);
                                    crate::leanh::lean_inc(v_v_1920_);
                                    crate::leanh::lean_inc(v_k_1919_);
                                    crate::leanh::lean_dec(v_impl_1830_);
                                    v___x_1922_ = crate::leanh::lean_box(0);
                                    v_isShared_1923_ = v_isSharedCheck_1931_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1934_ = crate::leanh::lean_ctor_get(v_impl_1830_, 4);
                                crate::leanh::lean_inc(v_r_1934_);
                                if crate::leanh::lean_obj_tag(v_r_1934_) == 0 {
                                    v_k_1935_ = crate::leanh::lean_ctor_get(v_impl_1830_, 1);
                                    v_v_1936_ = crate::leanh::lean_ctor_get(v_impl_1830_, 2);
                                    v_isSharedCheck_1959_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1830_)) as u8;
                                    if v_isSharedCheck_1959_ == 0 {
                                        v_unused_1960_ =
                                            crate::leanh::lean_ctor_get(v_impl_1830_, 4);
                                        crate::leanh::lean_dec(v_unused_1960_);
                                        v_unused_1961_ =
                                            crate::leanh::lean_ctor_get(v_impl_1830_, 3);
                                        crate::leanh::lean_dec(v_unused_1961_);
                                        v_unused_1962_ =
                                            crate::leanh::lean_ctor_get(v_impl_1830_, 0);
                                        crate::leanh::lean_dec(v_unused_1962_);
                                        v___x_1938_ = v_impl_1830_;
                                        v_isShared_1939_ = v_isSharedCheck_1959_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1936_);
                                        crate::leanh::lean_inc(v_k_1935_);
                                        crate::leanh::lean_dec(v_impl_1830_);
                                        v___x_1938_ = crate::leanh::lean_box(0);
                                        v_isShared_1939_ = v_isSharedCheck_1959_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1963_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1828_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1827_, 4, v_r_1934_);
                                        crate::leanh::lean_ctor_set(v___x_1827_, 3, v_impl_1830_);
                                        crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1963_);
                                        v___x_1965_ = v___x_1827_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1966_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1966_,
                                            0,
                                            v___x_1963_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1966_,
                                            1,
                                            v_k_1822_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1966_,
                                            2,
                                            v_v_1823_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1966_,
                                            3,
                                            v_impl_1830_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1966_,
                                            4,
                                            v_r_1934_,
                                        );
                                        v___x_1965_ = v_reuseFailAlloc_1966_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_1823_);
                        crate::leanh::lean_dec(v_k_1822_);
                        if v_isShared_1828_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1827_, 2, v_v_1819_);
                            crate::leanh::lean_ctor_set(v___x_1827_, 1, v_k_1818_);
                            v___x_1968_ = v___x_1827_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1969_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_size_1821_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_k_1818_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_v_1819_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_l_1824_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 4, v_r_1825_);
                            v___x_1968_ = v_reuseFailAlloc_1969_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_1821_);
                        v_impl_1970_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_1818_, v_v_1819_, v_r_1825_);
                        v___x_1971_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_1824_) == 0 {
                            v_size_1972_ = crate::leanh::lean_ctor_get(v_l_1824_, 0);
                            v_size_1973_ = crate::leanh::lean_ctor_get(v_impl_1970_, 0);
                            crate::leanh::lean_inc(v_size_1973_);
                            v_k_1974_ = crate::leanh::lean_ctor_get(v_impl_1970_, 1);
                            crate::leanh::lean_inc(v_k_1974_);
                            v_v_1975_ = crate::leanh::lean_ctor_get(v_impl_1970_, 2);
                            crate::leanh::lean_inc(v_v_1975_);
                            v_l_1976_ = crate::leanh::lean_ctor_get(v_impl_1970_, 3);
                            crate::leanh::lean_inc(v_l_1976_);
                            v_r_1977_ = crate::leanh::lean_ctor_get(v_impl_1970_, 4);
                            crate::leanh::lean_inc(v_r_1977_);
                            v___x_1978_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1979_ = lean_nat_mul(v___x_1978_, v_size_1972_);
                            v___x_1980_ = lean_nat_dec_lt(v___x_1979_, v_size_1973_);
                            crate::leanh::lean_dec(v___x_1979_);
                            if v___x_1980_ == 0 {
                                crate::leanh::lean_dec(v_r_1977_);
                                crate::leanh::lean_dec(v_l_1976_);
                                crate::leanh::lean_dec(v_v_1975_);
                                crate::leanh::lean_dec(v_k_1974_);
                                v___x_1981_ = lean_nat_add(v___x_1971_, v_size_1972_);
                                v___x_1982_ = lean_nat_add(v___x_1981_, v_size_1973_);
                                crate::leanh::lean_dec(v_size_1973_);
                                crate::leanh::lean_dec(v___x_1981_);
                                if v_isShared_1828_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1827_, 4, v_impl_1970_);
                                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1982_);
                                    v___x_1984_ = v___x_1827_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1985_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1985_,
                                        0,
                                        v___x_1982_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1985_,
                                        1,
                                        v_k_1822_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1985_,
                                        2,
                                        v_v_1823_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1985_,
                                        3,
                                        v_l_1824_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1985_,
                                        4,
                                        v_impl_1970_,
                                    );
                                    v___x_1984_ = v_reuseFailAlloc_1985_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2049_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1970_)) as u8;
                                if v_isSharedCheck_2049_ == 0 {
                                    v_unused_2050_ = crate::leanh::lean_ctor_get(v_impl_1970_, 4);
                                    crate::leanh::lean_dec(v_unused_2050_);
                                    v_unused_2051_ = crate::leanh::lean_ctor_get(v_impl_1970_, 3);
                                    crate::leanh::lean_dec(v_unused_2051_);
                                    v_unused_2052_ = crate::leanh::lean_ctor_get(v_impl_1970_, 2);
                                    crate::leanh::lean_dec(v_unused_2052_);
                                    v_unused_2053_ = crate::leanh::lean_ctor_get(v_impl_1970_, 1);
                                    crate::leanh::lean_dec(v_unused_2053_);
                                    v_unused_2054_ = crate::leanh::lean_ctor_get(v_impl_1970_, 0);
                                    crate::leanh::lean_dec(v_unused_2054_);
                                    v___x_1987_ = v_impl_1970_;
                                    v_isShared_1988_ = v_isSharedCheck_2049_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1970_);
                                    v___x_1987_ = crate::leanh::lean_box(0);
                                    v_isShared_1988_ = v_isSharedCheck_2049_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2055_ = crate::leanh::lean_ctor_get(v_impl_1970_, 3);
                            crate::leanh::lean_inc(v_l_2055_);
                            if crate::leanh::lean_obj_tag(v_l_2055_) == 0 {
                                v_r_2056_ = crate::leanh::lean_ctor_get(v_impl_1970_, 4);
                                v_k_2057_ = crate::leanh::lean_ctor_get(v_impl_1970_, 1);
                                v_v_2058_ = crate::leanh::lean_ctor_get(v_impl_1970_, 2);
                                v_isSharedCheck_2081_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1970_)) as u8;
                                if v_isSharedCheck_2081_ == 0 {
                                    v_unused_2082_ = crate::leanh::lean_ctor_get(v_impl_1970_, 3);
                                    crate::leanh::lean_dec(v_unused_2082_);
                                    v_unused_2083_ = crate::leanh::lean_ctor_get(v_impl_1970_, 0);
                                    crate::leanh::lean_dec(v_unused_2083_);
                                    v___x_2060_ = v_impl_1970_;
                                    v_isShared_2061_ = v_isSharedCheck_2081_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2056_);
                                    crate::leanh::lean_inc(v_v_2058_);
                                    crate::leanh::lean_inc(v_k_2057_);
                                    crate::leanh::lean_dec(v_impl_1970_);
                                    v___x_2060_ = crate::leanh::lean_box(0);
                                    v_isShared_2061_ = v_isSharedCheck_2081_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_2084_ = crate::leanh::lean_ctor_get(v_impl_1970_, 4);
                                crate::leanh::lean_inc(v_r_2084_);
                                if crate::leanh::lean_obj_tag(v_r_2084_) == 0 {
                                    v_k_2085_ = crate::leanh::lean_ctor_get(v_impl_1970_, 1);
                                    v_v_2086_ = crate::leanh::lean_ctor_get(v_impl_1970_, 2);
                                    v_isSharedCheck_2097_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1970_)) as u8;
                                    if v_isSharedCheck_2097_ == 0 {
                                        v_unused_2098_ =
                                            crate::leanh::lean_ctor_get(v_impl_1970_, 4);
                                        crate::leanh::lean_dec(v_unused_2098_);
                                        v_unused_2099_ =
                                            crate::leanh::lean_ctor_get(v_impl_1970_, 3);
                                        crate::leanh::lean_dec(v_unused_2099_);
                                        v_unused_2100_ =
                                            crate::leanh::lean_ctor_get(v_impl_1970_, 0);
                                        crate::leanh::lean_dec(v_unused_2100_);
                                        v___x_2088_ = v_impl_1970_;
                                        v_isShared_2089_ = v_isSharedCheck_2097_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2086_);
                                        crate::leanh::lean_inc(v_k_2085_);
                                        crate::leanh::lean_dec(v_impl_1970_);
                                        v___x_2088_ = crate::leanh::lean_box(0);
                                        v_isShared_2089_ = v_isSharedCheck_2097_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_2101_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1828_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1827_, 4, v_impl_1970_);
                                        crate::leanh::lean_ctor_set(v___x_1827_, 3, v_r_2084_);
                                        crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_2101_);
                                        v___x_2103_ = v___x_1827_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2104_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2104_,
                                            0,
                                            v___x_2101_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2104_,
                                            1,
                                            v_k_1822_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2104_,
                                            2,
                                            v_v_1823_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2104_,
                                            3,
                                            v_r_2084_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2104_,
                                            4,
                                            v_impl_1970_,
                                        );
                                        v___x_2103_ = v_reuseFailAlloc_2104_;
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
                return v___x_1844_;
            }
            3 => {
                v_size_1849_ = crate::leanh::lean_ctor_get(v_l_1836_, 0);
                v_size_1850_ = crate::leanh::lean_ctor_get(v_r_1837_, 0);
                v_k_1851_ = crate::leanh::lean_ctor_get(v_r_1837_, 1);
                v_v_1852_ = crate::leanh::lean_ctor_get(v_r_1837_, 2);
                v_l_1853_ = crate::leanh::lean_ctor_get(v_r_1837_, 3);
                v_r_1854_ = crate::leanh::lean_ctor_get(v_r_1837_, 4);
                v___x_1855_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1856_ = lean_nat_mul(v___x_1855_, v_size_1849_);
                v___x_1857_ = lean_nat_dec_lt(v_size_1850_, v___x_1856_);
                crate::leanh::lean_dec(v___x_1856_);
                if v___x_1857_ == 0 {
                    crate::leanh::lean_inc(v_r_1854_);
                    crate::leanh::lean_inc(v_l_1853_);
                    crate::leanh::lean_inc(v_v_1852_);
                    crate::leanh::lean_inc(v_k_1851_);
                    v_isSharedCheck_1886_ = (!crate::leanh::lean_is_exclusive(v_r_1837_)) as u8;
                    if v_isSharedCheck_1886_ == 0 {
                        v_unused_1887_ = crate::leanh::lean_ctor_get(v_r_1837_, 4);
                        crate::leanh::lean_dec(v_unused_1887_);
                        v_unused_1888_ = crate::leanh::lean_ctor_get(v_r_1837_, 3);
                        crate::leanh::lean_dec(v_unused_1888_);
                        v_unused_1889_ = crate::leanh::lean_ctor_get(v_r_1837_, 2);
                        crate::leanh::lean_dec(v_unused_1889_);
                        v_unused_1890_ = crate::leanh::lean_ctor_get(v_r_1837_, 1);
                        crate::leanh::lean_dec(v_unused_1890_);
                        v_unused_1891_ = crate::leanh::lean_ctor_get(v_r_1837_, 0);
                        crate::leanh::lean_dec(v_unused_1891_);
                        v___x_1859_ = v_r_1837_;
                        v_isShared_1860_ = v_isSharedCheck_1886_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1837_);
                        v___x_1859_ = crate::leanh::lean_box(0);
                        v_isShared_1860_ = v_isSharedCheck_1886_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1827_);
                    v___x_1892_ = lean_nat_add(v___x_1831_, v_size_1833_);
                    crate::leanh::lean_dec(v_size_1833_);
                    v___x_1893_ = lean_nat_add(v___x_1892_, v_size_1832_);
                    crate::leanh::lean_dec(v___x_1892_);
                    v___x_1894_ = lean_nat_add(v___x_1831_, v_size_1832_);
                    v___x_1895_ = lean_nat_add(v___x_1894_, v_size_1850_);
                    crate::leanh::lean_dec(v___x_1894_);
                    crate::leanh::lean_inc_ref(v_r_1825_);
                    if v_isShared_1848_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1847_, 4, v_r_1825_);
                        crate::leanh::lean_ctor_set(v___x_1847_, 3, v_r_1837_);
                        crate::leanh::lean_ctor_set(v___x_1847_, 2, v_v_1823_);
                        crate::leanh::lean_ctor_set(v___x_1847_, 1, v_k_1822_);
                        crate::leanh::lean_ctor_set(v___x_1847_, 0, v___x_1895_);
                        v___x_1897_ = v___x_1847_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1910_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1895_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_k_1822_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_v_1823_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 3, v_r_1837_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 4, v_r_1825_);
                        v___x_1897_ = v_reuseFailAlloc_1910_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1861_ = lean_nat_add(v___x_1831_, v_size_1833_);
                crate::leanh::lean_dec(v_size_1833_);
                v___x_1862_ = lean_nat_add(v___x_1861_, v_size_1832_);
                crate::leanh::lean_dec(v___x_1861_);
                v___x_1874_ = lean_nat_add(v___x_1831_, v_size_1849_);
                if crate::leanh::lean_obj_tag(v_l_1853_) == 0 {
                    v_size_1884_ = crate::leanh::lean_ctor_get(v_l_1853_, 0);
                    crate::leanh::lean_inc(v_size_1884_);
                    v___y_1876_ = v_size_1884_;
                    state = 8;
                    continue;
                } else {
                    v___x_1885_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1876_ = v___x_1885_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1867_ = lean_nat_add(v___y_1864_, v___y_1866_);
                crate::leanh::lean_dec(v___y_1866_);
                crate::leanh::lean_dec(v___y_1864_);
                if v_isShared_1860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1859_, 4, v_r_1825_);
                    crate::leanh::lean_ctor_set(v___x_1859_, 3, v_r_1854_);
                    crate::leanh::lean_ctor_set(v___x_1859_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v___x_1859_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v___x_1859_, 0, v___x_1867_);
                    v___x_1869_ = v___x_1859_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1873_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 3, v_r_1854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 4, v_r_1825_);
                    v___x_1869_ = v_reuseFailAlloc_1873_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1848_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1847_, 4, v___x_1869_);
                    crate::leanh::lean_ctor_set(v___x_1847_, 3, v___y_1865_);
                    crate::leanh::lean_ctor_set(v___x_1847_, 2, v_v_1852_);
                    crate::leanh::lean_ctor_set(v___x_1847_, 1, v_k_1851_);
                    crate::leanh::lean_ctor_set(v___x_1847_, 0, v___x_1862_);
                    v___x_1871_ = v___x_1847_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_k_1851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_v_1852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 3, v___y_1865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 4, v___x_1869_);
                    v___x_1871_ = v_reuseFailAlloc_1872_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1871_;
            }
            8 => {
                v___x_1877_ = lean_nat_add(v___x_1874_, v___y_1876_);
                crate::leanh::lean_dec(v___y_1876_);
                crate::leanh::lean_dec(v___x_1874_);
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1827_, 4, v_l_1853_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 3, v_l_1836_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 2, v_v_1835_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 1, v_k_1834_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1877_);
                    v___x_1879_ = v___x_1827_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1883_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_k_1834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_v_1835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 3, v_l_1836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1883_, 4, v_l_1853_);
                    v___x_1879_ = v_reuseFailAlloc_1883_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1880_ = lean_nat_add(v___x_1831_, v_size_1832_);
                if crate::leanh::lean_obj_tag(v_r_1854_) == 0 {
                    v_size_1881_ = crate::leanh::lean_ctor_get(v_r_1854_, 0);
                    crate::leanh::lean_inc(v_size_1881_);
                    v___y_1864_ = v___x_1880_;
                    v___y_1865_ = v___x_1879_;
                    v___y_1866_ = v_size_1881_;
                    state = 5;
                    continue;
                } else {
                    v___x_1882_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1864_ = v___x_1880_;
                    v___y_1865_ = v___x_1879_;
                    v___y_1866_ = v___x_1882_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1904_ = (!crate::leanh::lean_is_exclusive(v_r_1825_)) as u8;
                if v_isSharedCheck_1904_ == 0 {
                    v_unused_1905_ = crate::leanh::lean_ctor_get(v_r_1825_, 4);
                    crate::leanh::lean_dec(v_unused_1905_);
                    v_unused_1906_ = crate::leanh::lean_ctor_get(v_r_1825_, 3);
                    crate::leanh::lean_dec(v_unused_1906_);
                    v_unused_1907_ = crate::leanh::lean_ctor_get(v_r_1825_, 2);
                    crate::leanh::lean_dec(v_unused_1907_);
                    v_unused_1908_ = crate::leanh::lean_ctor_get(v_r_1825_, 1);
                    crate::leanh::lean_dec(v_unused_1908_);
                    v_unused_1909_ = crate::leanh::lean_ctor_get(v_r_1825_, 0);
                    crate::leanh::lean_dec(v_unused_1909_);
                    v___x_1899_ = v_r_1825_;
                    v_isShared_1900_ = v_isSharedCheck_1904_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1825_);
                    v___x_1899_ = crate::leanh::lean_box(0);
                    v_isShared_1900_ = v_isSharedCheck_1904_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1900_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1899_, 4, v___x_1897_);
                    crate::leanh::lean_ctor_set(v___x_1899_, 3, v_l_1836_);
                    crate::leanh::lean_ctor_set(v___x_1899_, 2, v_v_1835_);
                    crate::leanh::lean_ctor_set(v___x_1899_, 1, v_k_1834_);
                    crate::leanh::lean_ctor_set(v___x_1899_, 0, v___x_1893_);
                    v___x_1902_ = v___x_1899_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1903_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_l_1836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 4, v___x_1897_);
                    v___x_1902_ = v_reuseFailAlloc_1903_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1902_;
            }
            13 => {
                v___x_1924_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_1918_);
                if v_isShared_1923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1922_, 3, v_r_1918_);
                    crate::leanh::lean_ctor_set(v___x_1922_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v___x_1922_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v___x_1922_, 0, v___x_1831_);
                    v___x_1926_ = v___x_1922_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_r_1918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_r_1918_);
                    v___x_1926_ = v_reuseFailAlloc_1930_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1827_, 4, v___x_1926_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 3, v_l_1917_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 2, v_v_1920_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 1, v_k_1919_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1924_);
                    v___x_1928_ = v___x_1827_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1929_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_k_1919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_v_1920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_l_1917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 4, v___x_1926_);
                    v___x_1928_ = v_reuseFailAlloc_1929_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1928_;
            }
            16 => {
                v_k_1940_ = crate::leanh::lean_ctor_get(v_r_1934_, 1);
                v_v_1941_ = crate::leanh::lean_ctor_get(v_r_1934_, 2);
                v_isSharedCheck_1955_ = (!crate::leanh::lean_is_exclusive(v_r_1934_)) as u8;
                if v_isSharedCheck_1955_ == 0 {
                    v_unused_1956_ = crate::leanh::lean_ctor_get(v_r_1934_, 4);
                    crate::leanh::lean_dec(v_unused_1956_);
                    v_unused_1957_ = crate::leanh::lean_ctor_get(v_r_1934_, 3);
                    crate::leanh::lean_dec(v_unused_1957_);
                    v_unused_1958_ = crate::leanh::lean_ctor_get(v_r_1934_, 0);
                    crate::leanh::lean_dec(v_unused_1958_);
                    v___x_1943_ = v_r_1934_;
                    v_isShared_1944_ = v_isSharedCheck_1955_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1941_);
                    crate::leanh::lean_inc(v_k_1940_);
                    crate::leanh::lean_dec(v_r_1934_);
                    v___x_1943_ = crate::leanh::lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1955_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1945_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1943_, 4, v_l_1917_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 3, v_l_1917_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 2, v_v_1936_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 1, v_k_1935_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1831_);
                    v___x_1947_ = v___x_1943_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_k_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_v_1936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_l_1917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_l_1917_);
                    v___x_1947_ = v_reuseFailAlloc_1954_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1939_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1938_, 4, v_l_1917_);
                    crate::leanh::lean_ctor_set(v___x_1938_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v___x_1938_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v___x_1938_, 0, v___x_1831_);
                    v___x_1949_ = v___x_1938_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1953_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 3, v_l_1917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 4, v_l_1917_);
                    v___x_1949_ = v_reuseFailAlloc_1953_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1827_, 4, v___x_1949_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 3, v___x_1947_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 2, v_v_1941_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 1, v_k_1940_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1945_);
                    v___x_1951_ = v___x_1827_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_k_1940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_v_1941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 3, v___x_1947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 4, v___x_1949_);
                    v___x_1951_ = v_reuseFailAlloc_1952_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1951_;
            }
            21 => {
                return v___x_1965_;
            }
            22 => {
                return v___x_1968_;
            }
            23 => {
                return v___x_1984_;
            }
            24 => {
                v_size_1989_ = crate::leanh::lean_ctor_get(v_l_1976_, 0);
                v_k_1990_ = crate::leanh::lean_ctor_get(v_l_1976_, 1);
                v_v_1991_ = crate::leanh::lean_ctor_get(v_l_1976_, 2);
                v_l_1992_ = crate::leanh::lean_ctor_get(v_l_1976_, 3);
                v_r_1993_ = crate::leanh::lean_ctor_get(v_l_1976_, 4);
                v_size_1994_ = crate::leanh::lean_ctor_get(v_r_1977_, 0);
                v___x_1995_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1996_ = lean_nat_mul(v___x_1995_, v_size_1994_);
                v___x_1997_ = lean_nat_dec_lt(v_size_1989_, v___x_1996_);
                crate::leanh::lean_dec(v___x_1996_);
                if v___x_1997_ == 0 {
                    crate::leanh::lean_inc(v_r_1993_);
                    crate::leanh::lean_inc(v_l_1992_);
                    crate::leanh::lean_inc(v_v_1991_);
                    crate::leanh::lean_inc(v_k_1990_);
                    v_isSharedCheck_2025_ = (!crate::leanh::lean_is_exclusive(v_l_1976_)) as u8;
                    if v_isSharedCheck_2025_ == 0 {
                        v_unused_2026_ = crate::leanh::lean_ctor_get(v_l_1976_, 4);
                        crate::leanh::lean_dec(v_unused_2026_);
                        v_unused_2027_ = crate::leanh::lean_ctor_get(v_l_1976_, 3);
                        crate::leanh::lean_dec(v_unused_2027_);
                        v_unused_2028_ = crate::leanh::lean_ctor_get(v_l_1976_, 2);
                        crate::leanh::lean_dec(v_unused_2028_);
                        v_unused_2029_ = crate::leanh::lean_ctor_get(v_l_1976_, 1);
                        crate::leanh::lean_dec(v_unused_2029_);
                        v_unused_2030_ = crate::leanh::lean_ctor_get(v_l_1976_, 0);
                        crate::leanh::lean_dec(v_unused_2030_);
                        v___x_1999_ = v_l_1976_;
                        v_isShared_2000_ = v_isSharedCheck_2025_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1976_);
                        v___x_1999_ = crate::leanh::lean_box(0);
                        v_isShared_2000_ = v_isSharedCheck_2025_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1827_);
                    v___x_2031_ = lean_nat_add(v___x_1971_, v_size_1972_);
                    v___x_2032_ = lean_nat_add(v___x_2031_, v_size_1973_);
                    crate::leanh::lean_dec(v_size_1973_);
                    v___x_2033_ = lean_nat_add(v___x_2031_, v_size_1989_);
                    crate::leanh::lean_dec(v___x_2031_);
                    crate::leanh::lean_inc_ref(v_l_1824_);
                    if v_isShared_1988_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1987_, 4, v_l_1976_);
                        crate::leanh::lean_ctor_set(v___x_1987_, 3, v_l_1824_);
                        crate::leanh::lean_ctor_set(v___x_1987_, 2, v_v_1823_);
                        crate::leanh::lean_ctor_set(v___x_1987_, 1, v_k_1822_);
                        crate::leanh::lean_ctor_set(v___x_1987_, 0, v___x_2033_);
                        v___x_2035_ = v___x_1987_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2033_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_1822_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_1823_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_l_1824_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_l_1976_);
                        v___x_2035_ = v_reuseFailAlloc_2048_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2001_ = lean_nat_add(v___x_1971_, v_size_1972_);
                v___x_2002_ = lean_nat_add(v___x_2001_, v_size_1973_);
                crate::leanh::lean_dec(v_size_1973_);
                if crate::leanh::lean_obj_tag(v_l_1992_) == 0 {
                    v_size_2023_ = crate::leanh::lean_ctor_get(v_l_1992_, 0);
                    crate::leanh::lean_inc(v_size_2023_);
                    v___y_2015_ = v_size_2023_;
                    state = 29;
                    continue;
                } else {
                    v___x_2024_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2015_ = v___x_2024_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2007_ = lean_nat_add(v___y_2005_, v___y_2006_);
                crate::leanh::lean_dec(v___y_2006_);
                crate::leanh::lean_dec(v___y_2005_);
                if v_isShared_2000_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1999_, 4, v_r_1977_);
                    crate::leanh::lean_ctor_set(v___x_1999_, 3, v_r_1993_);
                    crate::leanh::lean_ctor_set(v___x_1999_, 2, v_v_1975_);
                    crate::leanh::lean_ctor_set(v___x_1999_, 1, v_k_1974_);
                    crate::leanh::lean_ctor_set(v___x_1999_, 0, v___x_2007_);
                    v___x_2009_ = v___x_1999_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_k_1974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_v_1975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_r_1993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_r_1977_);
                    v___x_2009_ = v_reuseFailAlloc_2013_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1988_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1987_, 4, v___x_2009_);
                    crate::leanh::lean_ctor_set(v___x_1987_, 3, v___y_2004_);
                    crate::leanh::lean_ctor_set(v___x_1987_, 2, v_v_1991_);
                    crate::leanh::lean_ctor_set(v___x_1987_, 1, v_k_1990_);
                    crate::leanh::lean_ctor_set(v___x_1987_, 0, v___x_2002_);
                    v___x_2011_ = v___x_1987_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2012_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 3, v___y_2004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 4, v___x_2009_);
                    v___x_2011_ = v_reuseFailAlloc_2012_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2011_;
            }
            29 => {
                v___x_2016_ = lean_nat_add(v___x_2001_, v___y_2015_);
                crate::leanh::lean_dec(v___y_2015_);
                crate::leanh::lean_dec(v___x_2001_);
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1827_, 4, v_l_1992_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_2016_);
                    v___x_2018_ = v___x_1827_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_l_1824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_l_1992_);
                    v___x_2018_ = v_reuseFailAlloc_2022_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2019_ = lean_nat_add(v___x_1971_, v_size_1994_);
                if crate::leanh::lean_obj_tag(v_r_1993_) == 0 {
                    v_size_2020_ = crate::leanh::lean_ctor_get(v_r_1993_, 0);
                    crate::leanh::lean_inc(v_size_2020_);
                    v___y_2004_ = v___x_2018_;
                    v___y_2005_ = v___x_2019_;
                    v___y_2006_ = v_size_2020_;
                    state = 26;
                    continue;
                } else {
                    v___x_2021_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2004_ = v___x_2018_;
                    v___y_2005_ = v___x_2019_;
                    v___y_2006_ = v___x_2021_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2042_ = (!crate::leanh::lean_is_exclusive(v_l_1824_)) as u8;
                if v_isSharedCheck_2042_ == 0 {
                    v_unused_2043_ = crate::leanh::lean_ctor_get(v_l_1824_, 4);
                    crate::leanh::lean_dec(v_unused_2043_);
                    v_unused_2044_ = crate::leanh::lean_ctor_get(v_l_1824_, 3);
                    crate::leanh::lean_dec(v_unused_2044_);
                    v_unused_2045_ = crate::leanh::lean_ctor_get(v_l_1824_, 2);
                    crate::leanh::lean_dec(v_unused_2045_);
                    v_unused_2046_ = crate::leanh::lean_ctor_get(v_l_1824_, 1);
                    crate::leanh::lean_dec(v_unused_2046_);
                    v_unused_2047_ = crate::leanh::lean_ctor_get(v_l_1824_, 0);
                    crate::leanh::lean_dec(v_unused_2047_);
                    v___x_2037_ = v_l_1824_;
                    v_isShared_2038_ = v_isSharedCheck_2042_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1824_);
                    v___x_2037_ = crate::leanh::lean_box(0);
                    v_isShared_2038_ = v_isSharedCheck_2042_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2037_, 4, v_r_1977_);
                    crate::leanh::lean_ctor_set(v___x_2037_, 3, v___x_2035_);
                    crate::leanh::lean_ctor_set(v___x_2037_, 2, v_v_1975_);
                    crate::leanh::lean_ctor_set(v___x_2037_, 1, v_k_1974_);
                    crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2032_);
                    v___x_2040_ = v___x_2037_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_k_1974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_v_1975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 3, v___x_2035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_r_1977_);
                    v___x_2040_ = v_reuseFailAlloc_2041_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2040_;
            }
            34 => {
                v_k_2062_ = crate::leanh::lean_ctor_get(v_l_2055_, 1);
                v_v_2063_ = crate::leanh::lean_ctor_get(v_l_2055_, 2);
                v_isSharedCheck_2077_ = (!crate::leanh::lean_is_exclusive(v_l_2055_)) as u8;
                if v_isSharedCheck_2077_ == 0 {
                    v_unused_2078_ = crate::leanh::lean_ctor_get(v_l_2055_, 4);
                    crate::leanh::lean_dec(v_unused_2078_);
                    v_unused_2079_ = crate::leanh::lean_ctor_get(v_l_2055_, 3);
                    crate::leanh::lean_dec(v_unused_2079_);
                    v_unused_2080_ = crate::leanh::lean_ctor_get(v_l_2055_, 0);
                    crate::leanh::lean_dec(v_unused_2080_);
                    v___x_2065_ = v_l_2055_;
                    v_isShared_2066_ = v_isSharedCheck_2077_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2063_);
                    crate::leanh::lean_inc(v_k_2062_);
                    crate::leanh::lean_dec(v_l_2055_);
                    v___x_2065_ = crate::leanh::lean_box(0);
                    v_isShared_2066_ = v_isSharedCheck_2077_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2067_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_2056_, 2);
                if v_isShared_2066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2065_, 4, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2065_, 3, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2065_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v___x_2065_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v___x_2065_, 0, v___x_1971_);
                    v___x_2069_ = v___x_2065_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_1971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_r_2056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_r_2056_);
                    v___x_2069_ = v_reuseFailAlloc_2076_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_2056_);
                if v_isShared_2061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2060_, 3, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2060_, 0, v___x_1971_);
                    v___x_2071_ = v___x_2060_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2075_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_1971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_k_2057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_v_2058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_r_2056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_r_2056_);
                    v___x_2071_ = v_reuseFailAlloc_2075_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1827_, 4, v___x_2071_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 3, v___x_2069_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 2, v_v_2063_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 1, v_k_2062_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_2067_);
                    v___x_2073_ = v___x_1827_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_2062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_2063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 3, v___x_2069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 4, v___x_2071_);
                    v___x_2073_ = v_reuseFailAlloc_2074_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2073_;
            }
            39 => {
                v___x_2090_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2088_, 4, v_l_2055_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_1971_);
                    v___x_2092_ = v___x_2088_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2096_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_1971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_1823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_l_2055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_l_2055_);
                    v___x_2092_ = v_reuseFailAlloc_2096_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1827_, 4, v_r_2084_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 3, v___x_2092_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 2, v_v_2086_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 1, v_k_2085_);
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_2090_);
                    v___x_2094_ = v___x_1827_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_k_2085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_v_2086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 3, v___x_2092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_r_2084_);
                    v___x_2094_ = v_reuseFailAlloc_2095_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2094_;
            }
            42 => {
                return v___x_2103_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_ExternLib_initFacetConfigs___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ = crate::leanh::lean_box(1);
    v___x_2109_ = l_Lake_ExternLib_defaultFacetConfig;
    v___x_2110_ = l_Lake_ExternLib_defaultFacet;
    v___x_2111_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_2110_, v___x_2109_, v___x_2108_);
    return v___x_2111_;
}
pub unsafe fn _init_l_Lake_ExternLib_initFacetConfigs___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ExternLib_initFacetConfigs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_ExternLib_initFacetConfigs___closed__0_once),
        _init_l_Lake_ExternLib_initFacetConfigs___closed__0,
    );
    v___x_2113_ = l_Lake_ExternLib_staticFacetConfig;
    v___x_2114_ = l_Lake_ExternLib_staticFacet;
    v___x_2115_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_2114_, v___x_2113_, v___x_2112_);
    return v___x_2115_;
}
pub unsafe fn _init_l_Lake_ExternLib_initFacetConfigs___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2116_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ExternLib_initFacetConfigs___closed__1),
        core::ptr::addr_of_mut!(l_Lake_ExternLib_initFacetConfigs___closed__1_once),
        _init_l_Lake_ExternLib_initFacetConfigs___closed__1,
    );
    v___x_2117_ = l_Lake_ExternLib_sharedFacetConfig;
    v___x_2118_ = l_Lake_ExternLib_sharedFacet;
    v___x_2119_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_2118_, v___x_2117_, v___x_2116_);
    return v___x_2119_;
}
pub unsafe fn _init_l_Lake_ExternLib_initFacetConfigs___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ExternLib_initFacetConfigs___closed__2),
        core::ptr::addr_of_mut!(l_Lake_ExternLib_initFacetConfigs___closed__2_once),
        _init_l_Lake_ExternLib_initFacetConfigs___closed__2,
    );
    v___x_2121_ = l_Lake_ExternLib_dynlibFacetConfig;
    v___x_2122_ = l_Lake_ExternLib_dynlibFacet;
    v___x_2123_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_2122_, v___x_2121_, v___x_2120_);
    return v___x_2123_;
}
pub unsafe fn _init_l_Lake_ExternLib_initFacetConfigs() -> *mut crate::leanh::LeanObject {
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2124_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ExternLib_initFacetConfigs___closed__3),
        core::ptr::addr_of_mut!(l_Lake_ExternLib_initFacetConfigs___closed__3_once),
        _init_l_Lake_ExternLib_initFacetConfigs___closed__3,
    );
    return v___x_2124_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(
    mut v_00_u03b2_2125_: *mut crate::leanh::LeanObject,
    mut v_k_2126_: *mut crate::leanh::LeanObject,
    mut v_v_2127_: *mut crate::leanh::LeanObject,
    mut v_t_2128_: *mut crate::leanh::LeanObject,
    mut v_hl_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_2126_, v_v_2127_, v_t_2128_);
    return v___x_2130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_ExternLib(
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
    res = runtime_initialize_Lake_Build_Job_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Register(builtin);
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
    l_Lake_ExternLib_staticFacetConfig = _init_l_Lake_ExternLib_staticFacetConfig();
    crate::leanh::lean_mark_persistent(l_Lake_ExternLib_staticFacetConfig);
    l_Lake_ExternLib_sharedFacetConfig = _init_l_Lake_ExternLib_sharedFacetConfig();
    crate::leanh::lean_mark_persistent(l_Lake_ExternLib_sharedFacetConfig);
    l_Lake_ExternLib_dynlibFacetConfig = _init_l_Lake_ExternLib_dynlibFacetConfig();
    crate::leanh::lean_mark_persistent(l_Lake_ExternLib_dynlibFacetConfig);
    l_Lake_ExternLib_defaultFacetConfig = _init_l_Lake_ExternLib_defaultFacetConfig();
    crate::leanh::lean_mark_persistent(l_Lake_ExternLib_defaultFacetConfig);
    l_Lake_ExternLib_initFacetConfigs = _init_l_Lake_ExternLib_initFacetConfigs();
    crate::leanh::lean_mark_persistent(l_Lake_ExternLib_initFacetConfigs);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_ExternLib(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_ExternLib(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lake_Build_Job_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Register(builtin);
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
    res = runtime_initialize_Lake_Build_ExternLib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_ExternLib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_ExternLib(builtin);
}
