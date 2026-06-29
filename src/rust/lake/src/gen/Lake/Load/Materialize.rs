// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: Lake.Config.Env Lake.Load.Manifest Lake.Config.Package Lake.Util.Git Lake.Util.IO Lake.Reservoir
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed, lean_io_realpath,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_string_append, lean_string_dec_eq,
    lean_string_memcmp, lean_string_utf8_byte_size, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instDecidableEq___redArg;
use crate::r#gen::Init::Data::Repr::l_String_quote;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{l_ReaderT_instMonad___redArg, l_instDecidableEqString___boxed};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_removeDirAll, l_System_FilePath_isDir, l_instMonadEIO,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::System::Platform::l_System_Platform_isWindows;
use crate::r#gen::Lake::Config::Defaults::{l_Lake_defaultConfigFile, l_Lake_defaultManifestFile};
use crate::r#gen::Lake::Config::Env::{
    initialize_Lake_Config_Env, runtime_initialize_Lake_Config_Env,
};
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, runtime_initialize_Lake_Config_Package,
};
use crate::r#gen::Lake::Load::Manifest::{
    initialize_Lake_Load_Manifest, l_Lake_Manifest_load, l_Lake_instInhabitedPackageEntry_default,
    runtime_initialize_Lake_Load_Manifest,
};
use crate::r#gen::Lake::Reservoir::{
    initialize_Lake_Reservoir, l_Lake_RegistryPkg_gitSrc_x3f, l_Lake_Reservoir_fetchPkg_x3f,
    l_Lake_Reservoir_fetchPkgVersions, runtime_initialize_Lake_Reservoir,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lake::Util::Git::{
    initialize_Lake_Util_Git, l_Lake_Git_defaultRemote, l_Lake_Git_filterUrl_x3f,
    l_Lake_GitRepo_checkoutDetach, l_Lake_GitRepo_clean, l_Lake_GitRepo_clone,
    l_Lake_GitRepo_findRemoteRevision, l_Lake_GitRepo_getHeadRevision,
    l_Lake_GitRepo_getRemoteUrl_x3f, l_Lake_GitRepo_hasNoDiff,
    l_Lake_GitRepo_resolveRemoteRevision, l_Lake_GitRepo_resolveRevision_x3f,
    runtime_initialize_Lake_Util_Git,
};
use crate::r#gen::Lake::Util::IO::{
    initialize_Lake_Util_IO, l_Lake_resolvePath, runtime_initialize_Lake_Util_IO,
};
use crate::r#gen::Lake::Util::Version::{
    l_Lake_StdVer_toString, l_Lake_VerRange_parse, l_Lake_VerRange_test,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        58, 32, 114, 101, 112, 111, 115, 105, 116, 111, 114, 121, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value:
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
        39, 32, 104, 97, 115, 32, 108, 111, 99, 97, 108, 32, 99, 104, 97, 110, 103, 101, 115, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value:
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
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
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
        58, 32, 99, 104, 101, 99, 107, 105, 110, 103, 32, 111, 117, 116, 32, 114, 101, 118, 105,
        115, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value:
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
    m_data: [39, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [58, 32, 99, 108, 111, 110, 105, 110, 103, 32, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        58, 32, 85, 82, 76, 32, 104, 97, 115, 32, 99, 104, 97, 110, 103, 101, 100, 59, 32, 100,
        101, 108, 101, 116, 105, 110, 103, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1_value:
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
        39, 32, 97, 110, 100, 32, 99, 108, 111, 110, 105, 110, 103, 32, 97, 103, 97, 105, 110, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        58, 32, 85, 82, 76, 32, 104, 97, 115, 32, 99, 104, 97, 110, 103, 101, 100, 59, 32, 121,
        111, 117, 32, 109, 105, 103, 104, 116, 32, 110, 101, 101, 100, 32, 116, 111, 32, 100, 101,
        108, 101, 116, 101, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [39, 32, 109, 97, 110, 117, 97, 108, 108, 121, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5: u8 = 0;
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6: u8 = 0;
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7: usize = 0;
pub static l_Lake_instInhabitedMaterializedDep_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lake_instInhabitedMaterializedDep_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedMaterializedDep_default___closed__1_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96,
        32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
    ],
};
static mut l_Lake_instInhabitedMaterializedDep_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedMaterializedDep_default___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedMaterializedDep_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedMaterializedDep_default___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedMaterializedDep_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedMaterializedDep_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedMaterializedDep_default___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedMaterializedDep_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedMaterializedDep: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0_value:
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
    m_data: [47, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1_value:
    crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 158,
    m_capacity: 158,
    m_length: 157,
    m_data: [
        58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32,
        111, 110, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 46, 10, 10, 32, 32, 73, 102, 32,
        116, 104, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 105, 115, 32, 111, 110, 32, 71, 105,
        116, 72, 117, 98, 44, 32, 121, 111, 117, 32, 99, 97, 110, 32, 97, 100, 100, 32, 97, 32, 71,
        105, 116, 32, 115, 111, 117, 114, 99, 101, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109,
        112, 108, 101, 58, 10, 10, 32, 32, 32, 32, 114, 101, 113, 117, 105, 114, 101, 32, 46, 46,
        46, 10, 32, 32, 32, 32, 32, 32, 102, 114, 111, 109, 32, 103, 105, 116, 32, 34, 104, 116,
        116, 112, 115, 58, 47, 47, 103, 105, 116, 104, 117, 98, 46, 99, 111, 109, 47, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2_value:
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
    m_data: [34, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3_value:
    crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 71,
    m_capacity: 71,
    m_length: 70,
    m_data: [
        10, 10, 32, 32, 111, 114, 44, 32, 105, 102, 32, 117, 115, 105, 110, 103, 32, 84, 79, 77,
        76, 58, 10, 10, 32, 32, 32, 32, 91, 91, 114, 101, 113, 117, 105, 114, 101, 93, 93, 10, 32,
        32, 32, 32, 103, 105, 116, 32, 61, 32, 34, 104, 116, 116, 112, 115, 58, 47, 47, 103, 105,
        116, 104, 117, 98, 46, 99, 111, 109, 47, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [10, 32, 32, 32, 32, 46, 46, 46, 10, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 64, 32, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [10, 32, 32, 32, 32, 114, 101, 118, 32, 61, 32, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        10, 32, 32, 32, 32, 118, 101, 114, 115, 105, 111, 110, 32, 61, 32, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58, 32, 0]};
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [103, 105, 116, 35, 0]};
static mut l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__0_value: crate::leanh::LeanStringObject<36> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            58, 32, 71, 105, 116, 32, 115, 111, 117, 114, 99, 101, 32, 110, 111, 116, 32, 102, 111,
            117, 110, 100, 32, 111, 110, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [58, 32, 118, 101, 114, 115, 105, 111, 110, 32, 96, 0],
    };
static mut l_Lake_Dependency_materialize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__2_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            96, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 111, 110, 32, 82, 101, 115,
            101, 114, 118, 111, 105, 114, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__3_value: crate::leanh::LeanStringObject<96> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 96,
        m_capacity: 96,
        m_length: 95,
        m_data: [
            58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 101, 116, 99, 104, 32, 112,
            97, 99, 107, 97, 103, 101, 32, 118, 101, 114, 115, 105, 111, 110, 115, 58, 32, 116,
            104, 105, 115, 32, 109, 97, 121, 32, 98, 101, 32, 97, 32, 116, 114, 97, 110, 115, 105,
            101, 110, 116, 32, 101, 114, 114, 111, 114, 32, 111, 114, 32, 97, 32, 98, 117, 103, 32,
            105, 110, 32, 76, 97, 107, 101, 32, 111, 114, 32, 82, 101, 115, 101, 114, 118, 111,
            105, 114, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__4_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            58, 32, 117, 115, 105, 110, 103, 32, 118, 101, 114, 115, 105, 111, 110, 32, 96, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__5_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            96, 32, 97, 116, 32, 114, 101, 118, 105, 115, 105, 111, 110, 32, 96, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__6_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lake_Dependency_materialize___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__7_value: crate::leanh::LeanStringObject<93> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 93,
        m_capacity: 93,
        m_length: 92,
        m_data: [
            58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 109, 97, 116, 101, 114, 105, 97,
            108, 105, 122, 101, 32, 112, 97, 99, 107, 97, 103, 101, 58, 32, 116, 104, 105, 115, 32,
            109, 97, 121, 32, 98, 101, 32, 97, 32, 116, 114, 97, 110, 115, 105, 101, 110, 116, 32,
            101, 114, 114, 111, 114, 32, 111, 114, 32, 97, 32, 98, 117, 103, 32, 105, 110, 32, 76,
            97, 107, 101, 32, 111, 114, 32, 82, 101, 115, 101, 114, 118, 111, 105, 114, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__8_value: crate::leanh::LeanStringObject<37> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 100, 101, 112, 101, 110, 100, 101, 110,
            99, 121, 32, 118, 101, 114, 115, 105, 111, 110, 32, 114, 97, 110, 103, 101, 58, 32, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dependency_materialize___closed__9_value: crate::leanh::LeanStringObject<93> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 93,
        m_capacity: 93,
        m_length: 92,
        m_data: [
            58, 32, 105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 100, 101, 112, 101, 110,
            100, 101, 110, 99, 121, 58, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 121, 32,
            105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 97, 32, 115, 111, 117, 114, 99,
            101, 32, 97, 110, 100, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 97, 32,
            115, 99, 111, 112, 101, 32, 102, 111, 114, 32, 82, 101, 115, 101, 114, 118, 111, 105,
            114, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 11 }, m_objs: [core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__0_value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_materialize___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [72, 69, 65, 68, 0],
    };
static mut l_Lake_PackageEntry_materialize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_materialize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(
    mut v_as_2922_: *mut crate::leanh::LeanObject,
    mut v_i_2923_: usize,
    mut v_stop_2924_: usize,
    mut v_b_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2928_: u8 = 0;
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: usize = 0;
    let mut v___x_2932_: usize = 0;
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2928_ = lean_usize_dec_eq(v_i_2923_, v_stop_2924_);
                if v___x_2928_ == 0 {
                    v___x_2929_ = lean_array_uget_borrowed(v_as_2922_, v_i_2923_);
                    crate::leanh::lean_inc_ref(v___y_2926_);
                    crate::leanh::lean_inc(v___x_2929_);
                    v___x_2930_ = crate::leanh::lean_apply_2(
                        v___y_2926_,
                        v___x_2929_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_2931_ = 1usize;
                    v___x_2932_ = lean_usize_add(v_i_2923_, v___x_2931_);
                    v_i_2923_ = v___x_2932_;
                    v_b_2925_ = v___x_2930_;
                    state = 0;
                    continue;
                } else {
                    v___x_2934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2934_, 0, v_b_2925_);
                    return v___x_2934_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(
    mut v_as_2935_: *mut crate::leanh::LeanObject,
    mut v_i_2936_: *mut crate::leanh::LeanObject,
    mut v_stop_2937_: *mut crate::leanh::LeanObject,
    mut v_b_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
    mut v___y_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2941_: usize = 0;
    let mut v_stop_boxed_2942_: usize = 0;
    let mut v_res_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2941_ = crate::leanh::lean_unbox_usize(v_i_2936_);
    crate::leanh::lean_dec(v_i_2936_);
    v_stop_boxed_2942_ = crate::leanh::lean_unbox_usize(v_stop_2937_);
    crate::leanh::lean_dec(v_stop_2937_);
    v_res_2943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_as_2935_, v_i_boxed_2941_, v_stop_boxed_2942_, v_b_2938_, v___y_2939_);
    crate::leanh::lean_dec_ref(v___y_2939_);
    crate::leanh::lean_dec_ref(v_as_2935_);
    return v_res_2943_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(
    mut v_name_2950_: *mut crate::leanh::LeanObject,
    mut v_repo_2951_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_2952_: *mut crate::leanh::LeanObject,
    mut v_a_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2956_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2971_: u8 = 0;
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: u8 = 0;
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2976_: usize = 0;
    let mut v___x_2977_: usize = 0;
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: usize = 0;
    let mut v___x_2980_: usize = 0;
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: u8 = 0;
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: usize = 0;
    let mut v___x_3001_: usize = 0;
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3009_: u8 = 0;
    let mut v_unused_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: usize = 0;
    let mut v___x_3012_: usize = 0;
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v_unused_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: usize = 0;
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: usize = 0;
    let mut v___x_3033_: usize = 0;
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: u8 = 0;
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: u8 = 0;
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: u8 = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: u8 = 0;
    let mut v___x_3057_: usize = 0;
    let mut v___x_3058_: usize = 0;
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: usize = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: u8 = 0;
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: usize = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: usize = 0;
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: usize = 0;
    let mut v___x_3104_: usize = 0;
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: usize = 0;
    let mut v___x_3114_: usize = 0;
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: usize = 0;
    let mut v___x_3117_: usize = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: u8 = 0;
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: usize = 0;
    let mut v___x_3124_: usize = 0;
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: usize = 0;
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: usize = 0;
    let mut v___x_3137_: usize = 0;
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: usize = 0;
    let mut v___x_3140_: usize = 0;
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3086_ = l_Lake_Git_defaultRemote;
                v___x_3087_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3088_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                crate::leanh::lean_inc_ref(v_repo_2951_);
                v___x_3089_ = l_Lake_GitRepo_findRemoteRevision(
                    v_repo_2951_,
                    v_rev_x3f_2952_,
                    v___x_3086_,
                    v___x_3088_,
                );
                if crate::leanh::lean_obj_tag(v___x_3089_) == 0 {
                    v_a_3090_ = crate::leanh::lean_ctor_get(v___x_3089_, 0);
                    crate::leanh::lean_inc(v_a_3090_);
                    v_a_3091_ = crate::leanh::lean_ctor_get(v___x_3089_, 1);
                    crate::leanh::lean_inc(v_a_3091_);
                    crate::leanh::lean_dec_ref_known(v___x_3089_, 2);
                    v___x_3119_ = lean_array_get_size(v_a_3091_);
                    v___x_3120_ = lean_nat_dec_lt(v___x_3087_, v___x_3119_);
                    if v___x_3120_ == 0 {
                        crate::leanh::lean_dec(v_a_3091_);
                        state = 14;
                        continue;
                    } else {
                        v___x_3121_ = crate::leanh::lean_box(0);
                        v___x_3122_ = lean_nat_dec_le(v___x_3119_, v___x_3119_);
                        if v___x_3122_ == 0 {
                            if v___x_3120_ == 0 {
                                crate::leanh::lean_dec(v_a_3091_);
                                state = 14;
                                continue;
                            } else {
                                v___x_3123_ = 0usize;
                                v___x_3124_ = lean_usize_of_nat(v___x_3119_);
                                v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3091_, v___x_3123_, v___x_3124_, v___x_3121_, v_a_2953_);
                                crate::leanh::lean_dec(v_a_3091_);
                                if crate::leanh::lean_obj_tag(v___x_3125_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3125_, 1);
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3090_);
                                    crate::leanh::lean_dec_ref(v_repo_2951_);
                                    crate::leanh::lean_dec_ref(v_name_2950_);
                                    return v___x_3125_;
                                }
                            }
                        } else {
                            v___x_3126_ = 0usize;
                            v___x_3127_ = lean_usize_of_nat(v___x_3119_);
                            v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3091_, v___x_3126_, v___x_3127_, v___x_3121_, v_a_2953_);
                            crate::leanh::lean_dec(v_a_3091_);
                            if crate::leanh::lean_obj_tag(v___x_3128_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3128_, 1);
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_3090_);
                                crate::leanh::lean_dec_ref(v_repo_2951_);
                                crate::leanh::lean_dec_ref(v_name_2950_);
                                return v___x_3128_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_repo_2951_);
                    crate::leanh::lean_dec_ref(v_name_2950_);
                    v_a_3129_ = crate::leanh::lean_ctor_get(v___x_3089_, 1);
                    crate::leanh::lean_inc(v_a_3129_);
                    crate::leanh::lean_dec_ref_known(v___x_3089_, 2);
                    v___x_3130_ = lean_array_get_size(v_a_3129_);
                    v___x_3131_ = lean_nat_dec_lt(v___x_3087_, v___x_3130_);
                    if v___x_3131_ == 0 {
                        crate::leanh::lean_dec(v_a_3129_);
                        v___x_3132_ = crate::leanh::lean_box(0);
                        v___x_3133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3133_, 0, v___x_3132_);
                        return v___x_3133_;
                    } else {
                        v___x_3134_ = crate::leanh::lean_box(0);
                        v___x_3135_ = lean_nat_dec_le(v___x_3130_, v___x_3130_);
                        if v___x_3135_ == 0 {
                            if v___x_3131_ == 0 {
                                crate::leanh::lean_dec(v_a_3129_);
                                state = 13;
                                continue;
                            } else {
                                v___x_3136_ = 0usize;
                                v___x_3137_ = lean_usize_of_nat(v___x_3130_);
                                v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3129_, v___x_3136_, v___x_3137_, v___x_3134_, v_a_2953_);
                                crate::leanh::lean_dec(v_a_3129_);
                                if crate::leanh::lean_obj_tag(v___x_3138_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3138_, 1);
                                    state = 13;
                                    continue;
                                } else {
                                    return v___x_3138_;
                                }
                            }
                        } else {
                            v___x_3139_ = 0usize;
                            v___x_3140_ = lean_usize_of_nat(v___x_3130_);
                            v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3129_, v___x_3139_, v___x_3140_, v___x_3134_, v_a_2953_);
                            crate::leanh::lean_dec(v_a_3129_);
                            if crate::leanh::lean_obj_tag(v___x_3141_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3141_, 1);
                                state = 13;
                                continue;
                            } else {
                                return v___x_3141_;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_a_2956_ == 0 {
                    crate::leanh::lean_dec_ref(v_repo_2951_);
                    crate::leanh::lean_dec_ref(v_name_2950_);
                    v___x_2957_ = crate::leanh::lean_box(0);
                    v___x_2958_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2958_, 0, v___x_2957_);
                    return v___x_2958_;
                } else {
                    v___x_2959_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
                    v___x_2960_ = lean_string_append(v_name_2950_, v___x_2959_);
                    v___x_2961_ = lean_string_append(v___x_2960_, v_repo_2951_);
                    crate::leanh::lean_dec_ref(v_repo_2951_);
                    v___x_2962_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
                    v___x_2963_ = lean_string_append(v___x_2961_, v___x_2962_);
                    v___x_2964_ = 2;
                    v___x_2965_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2965_, 0, v___x_2963_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2964_,
                    );
                    crate::leanh::lean_inc_ref(v_a_2953_);
                    v___x_2966_ = crate::leanh::lean_apply_2(
                        v_a_2953_,
                        v___x_2965_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_2967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2967_, 0, v___x_2966_);
                    return v___x_2967_;
                }
            }
            2 => {
                v___x_2972_ = lean_array_get_size(v___y_2970_);
                v___x_2973_ = lean_nat_dec_lt(v___y_2969_, v___x_2972_);
                if v___x_2973_ == 0 {
                    v_a_2956_ = v_val_2971_;
                    state = 1;
                    continue;
                } else {
                    v___x_2974_ = crate::leanh::lean_box(0);
                    v___x_2975_ = lean_nat_dec_le(v___x_2972_, v___x_2972_);
                    if v___x_2975_ == 0 {
                        if v___x_2973_ == 0 {
                            v_a_2956_ = v_val_2971_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2976_ = 0usize;
                            v___x_2977_ = lean_usize_of_nat(v___x_2972_);
                            v___x_2978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2970_, v___x_2976_, v___x_2977_, v___x_2974_, v_a_2953_);
                            if crate::leanh::lean_obj_tag(v___x_2978_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2978_, 1);
                                v_a_2956_ = v_val_2971_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_repo_2951_);
                                crate::leanh::lean_dec_ref(v_name_2950_);
                                return v___x_2978_;
                            }
                        }
                    } else {
                        v___x_2979_ = 0usize;
                        v___x_2980_ = lean_usize_of_nat(v___x_2972_);
                        v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2970_, v___x_2979_, v___x_2980_, v___x_2974_, v_a_2953_);
                        if crate::leanh::lean_obj_tag(v___x_2981_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2981_, 1);
                            v_a_2956_ = v_val_2971_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_repo_2951_);
                            crate::leanh::lean_dec_ref(v_name_2950_);
                            return v___x_2981_;
                        }
                    }
                }
            }
            3 => {
                v___x_2983_ = crate::leanh::lean_box(0);
                v___x_2984_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2984_, 0, v___x_2983_);
                return v___x_2984_;
            }
            4 => {
                v___x_2986_ = crate::leanh::lean_box(0);
                v___x_2987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2987_, 0, v___x_2986_);
                return v___x_2987_;
            }
            5 => {
                v___x_2989_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2990_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_2991_ = l_Lake_GitRepo_clean(v_repo_2951_, v___x_2990_);
                if crate::leanh::lean_obj_tag(v___x_2991_) == 0 {
                    v_a_2992_ = crate::leanh::lean_ctor_get(v___x_2991_, 0);
                    crate::leanh::lean_inc(v_a_2992_);
                    v_a_2993_ = crate::leanh::lean_ctor_get(v___x_2991_, 1);
                    crate::leanh::lean_inc(v_a_2993_);
                    crate::leanh::lean_dec_ref_known(v___x_2991_, 2);
                    v___x_2994_ = lean_array_get_size(v_a_2993_);
                    v___x_2995_ = lean_nat_dec_lt(v___x_2989_, v___x_2994_);
                    if v___x_2995_ == 0 {
                        crate::leanh::lean_dec(v_a_2993_);
                        v___x_2996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2996_, 0, v_a_2992_);
                        return v___x_2996_;
                    } else {
                        v___x_2997_ = crate::leanh::lean_box(0);
                        v___x_2998_ = lean_nat_dec_le(v___x_2994_, v___x_2994_);
                        if v___x_2998_ == 0 {
                            if v___x_2995_ == 0 {
                                crate::leanh::lean_dec(v_a_2993_);
                                v___x_2999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2999_, 0, v_a_2992_);
                                return v___x_2999_;
                            } else {
                                v___x_3000_ = 0usize;
                                v___x_3001_ = lean_usize_of_nat(v___x_2994_);
                                v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2993_, v___x_3000_, v___x_3001_, v___x_2997_, v_a_2953_);
                                crate::leanh::lean_dec(v_a_2993_);
                                if crate::leanh::lean_obj_tag(v___x_3002_) == 0 {
                                    v_isSharedCheck_3009_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3002_)) as u8;
                                    if v_isSharedCheck_3009_ == 0 {
                                        v_unused_3010_ =
                                            crate::leanh::lean_ctor_get(v___x_3002_, 0);
                                        crate::leanh::lean_dec(v_unused_3010_);
                                        v___x_3004_ = v___x_3002_;
                                        v_isShared_3005_ = v_isSharedCheck_3009_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_3002_);
                                        v___x_3004_ = crate::leanh::lean_box(0);
                                        v_isShared_3005_ = v_isSharedCheck_3009_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2992_);
                                    return v___x_3002_;
                                }
                            }
                        } else {
                            v___x_3011_ = 0usize;
                            v___x_3012_ = lean_usize_of_nat(v___x_2994_);
                            v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2993_, v___x_3011_, v___x_3012_, v___x_2997_, v_a_2953_);
                            crate::leanh::lean_dec(v_a_2993_);
                            if crate::leanh::lean_obj_tag(v___x_3013_) == 0 {
                                v_isSharedCheck_3020_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3013_)) as u8;
                                if v_isSharedCheck_3020_ == 0 {
                                    v_unused_3021_ = crate::leanh::lean_ctor_get(v___x_3013_, 0);
                                    crate::leanh::lean_dec(v_unused_3021_);
                                    v___x_3015_ = v___x_3013_;
                                    v_isShared_3016_ = v_isSharedCheck_3020_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3013_);
                                    v___x_3015_ = crate::leanh::lean_box(0);
                                    v_isShared_3016_ = v_isSharedCheck_3020_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2992_);
                                return v___x_3013_;
                            }
                        }
                    }
                } else {
                    v_a_3022_ = crate::leanh::lean_ctor_get(v___x_2991_, 1);
                    crate::leanh::lean_inc(v_a_3022_);
                    crate::leanh::lean_dec_ref_known(v___x_2991_, 2);
                    v___x_3023_ = lean_array_get_size(v_a_3022_);
                    v___x_3024_ = lean_nat_dec_lt(v___x_2989_, v___x_3023_);
                    if v___x_3024_ == 0 {
                        crate::leanh::lean_dec(v_a_3022_);
                        v___x_3025_ = crate::leanh::lean_box(0);
                        v___x_3026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3026_, 0, v___x_3025_);
                        return v___x_3026_;
                    } else {
                        v___x_3027_ = crate::leanh::lean_box(0);
                        v___x_3028_ = lean_nat_dec_le(v___x_3023_, v___x_3023_);
                        if v___x_3028_ == 0 {
                            if v___x_3024_ == 0 {
                                crate::leanh::lean_dec(v_a_3022_);
                                state = 4;
                                continue;
                            } else {
                                v___x_3029_ = 0usize;
                                v___x_3030_ = lean_usize_of_nat(v___x_3023_);
                                v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3022_, v___x_3029_, v___x_3030_, v___x_3027_, v_a_2953_);
                                crate::leanh::lean_dec(v_a_3022_);
                                if crate::leanh::lean_obj_tag(v___x_3031_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3031_, 1);
                                    state = 4;
                                    continue;
                                } else {
                                    return v___x_3031_;
                                }
                            }
                        } else {
                            v___x_3032_ = 0usize;
                            v___x_3033_ = lean_usize_of_nat(v___x_3023_);
                            v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3022_, v___x_3032_, v___x_3033_, v___x_3027_, v_a_2953_);
                            crate::leanh::lean_dec(v_a_3022_);
                            if crate::leanh::lean_obj_tag(v___x_3034_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3034_, 1);
                                state = 4;
                                continue;
                            } else {
                                return v___x_3034_;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_3005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3004_, 0, v_a_2992_);
                    v___x_3007_ = v___x_3004_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_2992_);
                    v___x_3007_ = v_reuseFailAlloc_3008_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3007_;
            }
            8 => {
                if v_isShared_3016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3015_, 0, v_a_2992_);
                    v___x_3018_ = v___x_3015_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_2992_);
                    v___x_3018_ = v_reuseFailAlloc_3019_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3018_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v___y_3036_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3036_, 1);
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_repo_2951_);
                    return v___y_3036_;
                }
            }
            11 => {
                v___x_3040_ = lean_string_dec_eq(v_a_3039_, v___y_3038_);
                crate::leanh::lean_dec_ref(v_a_3039_);
                if v___x_3040_ == 0 {
                    v___x_3041_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
                    v___x_3042_ = lean_string_append(v_name_2950_, v___x_3041_);
                    v___x_3043_ = lean_string_append(v___x_3042_, v___y_3038_);
                    v___x_3044_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
                    v___x_3045_ = lean_string_append(v___x_3043_, v___x_3044_);
                    v___x_3046_ = 1;
                    v___x_3047_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3047_, 0, v___x_3045_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3047_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3046_,
                    );
                    crate::leanh::lean_inc_ref(v_a_2953_);
                    v___x_3048_ = crate::leanh::lean_apply_2(
                        v_a_2953_,
                        v___x_3047_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_3049_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3050_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    crate::leanh::lean_inc_ref(v_repo_2951_);
                    v___x_3051_ =
                        l_Lake_GitRepo_checkoutDetach(v___y_3038_, v_repo_2951_, v___x_3050_);
                    if crate::leanh::lean_obj_tag(v___x_3051_) == 0 {
                        v_a_3052_ = crate::leanh::lean_ctor_get(v___x_3051_, 1);
                        crate::leanh::lean_inc(v_a_3052_);
                        crate::leanh::lean_dec_ref_known(v___x_3051_, 2);
                        v___x_3053_ = lean_array_get_size(v_a_3052_);
                        v___x_3054_ = lean_nat_dec_lt(v___x_3049_, v___x_3053_);
                        if v___x_3054_ == 0 {
                            crate::leanh::lean_dec(v_a_3052_);
                            state = 5;
                            continue;
                        } else {
                            v___x_3055_ = crate::leanh::lean_box(0);
                            v___x_3056_ = lean_nat_dec_le(v___x_3053_, v___x_3053_);
                            if v___x_3056_ == 0 {
                                if v___x_3054_ == 0 {
                                    crate::leanh::lean_dec(v_a_3052_);
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_3057_ = 0usize;
                                    v___x_3058_ = lean_usize_of_nat(v___x_3053_);
                                    v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3052_, v___x_3057_, v___x_3058_, v___x_3055_, v_a_2953_);
                                    crate::leanh::lean_dec(v_a_3052_);
                                    if crate::leanh::lean_obj_tag(v___x_3059_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3059_, 1);
                                        state = 5;
                                        continue;
                                    } else {
                                        v___y_3036_ = v___x_3059_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3060_ = 0usize;
                                v___x_3061_ = lean_usize_of_nat(v___x_3053_);
                                v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3052_, v___x_3060_, v___x_3061_, v___x_3055_, v_a_2953_);
                                crate::leanh::lean_dec(v_a_3052_);
                                if crate::leanh::lean_obj_tag(v___x_3062_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3062_, 1);
                                    state = 5;
                                    continue;
                                } else {
                                    v___y_3036_ = v___x_3062_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_3063_ = crate::leanh::lean_ctor_get(v___x_3051_, 1);
                        crate::leanh::lean_inc(v_a_3063_);
                        crate::leanh::lean_dec_ref_known(v___x_3051_, 2);
                        v___x_3064_ = lean_array_get_size(v_a_3063_);
                        v___x_3065_ = lean_nat_dec_lt(v___x_3049_, v___x_3064_);
                        if v___x_3065_ == 0 {
                            crate::leanh::lean_dec(v_a_3063_);
                            crate::leanh::lean_dec_ref(v_repo_2951_);
                            v___x_3066_ = crate::leanh::lean_box(0);
                            v___x_3067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3067_, 0, v___x_3066_);
                            return v___x_3067_;
                        } else {
                            v___x_3068_ = crate::leanh::lean_box(0);
                            v___x_3069_ = lean_nat_dec_le(v___x_3064_, v___x_3064_);
                            if v___x_3069_ == 0 {
                                if v___x_3065_ == 0 {
                                    crate::leanh::lean_dec(v_a_3063_);
                                    crate::leanh::lean_dec_ref(v_repo_2951_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3070_ = 0usize;
                                    v___x_3071_ = lean_usize_of_nat(v___x_3064_);
                                    v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3063_, v___x_3070_, v___x_3071_, v___x_3068_, v_a_2953_);
                                    crate::leanh::lean_dec(v_a_3063_);
                                    if crate::leanh::lean_obj_tag(v___x_3072_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3072_, 1);
                                        crate::leanh::lean_dec_ref(v_repo_2951_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___y_3036_ = v___x_3072_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3073_ = 0usize;
                                v___x_3074_ = lean_usize_of_nat(v___x_3064_);
                                v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3063_, v___x_3073_, v___x_3074_, v___x_3068_, v_a_2953_);
                                crate::leanh::lean_dec(v_a_3063_);
                                if crate::leanh::lean_obj_tag(v___x_3075_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3075_, 1);
                                    crate::leanh::lean_dec_ref(v_repo_2951_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___y_3036_ = v___x_3075_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3038_);
                    crate::leanh::lean_inc_ref(v_repo_2951_);
                    v___x_3076_ = l_Lake_GitRepo_hasNoDiff(v_repo_2951_);
                    v___x_3077_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3078_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    if v___x_3076_ == 0 {
                        v___y_2969_ = v___x_3077_;
                        v___y_2970_ = v___x_3078_;
                        v_val_2971_ = v___x_3040_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3079_ = 0;
                        v___y_2969_ = v___x_3077_;
                        v___y_2970_ = v___x_3078_;
                        v_val_2971_ = v___x_3079_;
                        state = 2;
                        continue;
                    }
                }
            }
            12 => {
                v___x_3081_ = crate::leanh::lean_box(0);
                v___x_3082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3082_, 0, v___x_3081_);
                return v___x_3082_;
            }
            13 => {
                v___x_3084_ = crate::leanh::lean_box(0);
                v___x_3085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3085_, 0, v___x_3084_);
                return v___x_3085_;
            }
            14 => {
                crate::leanh::lean_inc_ref(v_repo_2951_);
                v___x_3093_ = l_Lake_GitRepo_getHeadRevision(v_repo_2951_, v___x_3088_);
                if crate::leanh::lean_obj_tag(v___x_3093_) == 0 {
                    v_a_3094_ = crate::leanh::lean_ctor_get(v___x_3093_, 0);
                    crate::leanh::lean_inc(v_a_3094_);
                    v_a_3095_ = crate::leanh::lean_ctor_get(v___x_3093_, 1);
                    crate::leanh::lean_inc(v_a_3095_);
                    crate::leanh::lean_dec_ref_known(v___x_3093_, 2);
                    v___x_3096_ = lean_array_get_size(v_a_3095_);
                    v___x_3097_ = lean_nat_dec_lt(v___x_3087_, v___x_3096_);
                    if v___x_3097_ == 0 {
                        crate::leanh::lean_dec(v_a_3095_);
                        v___y_3038_ = v_a_3090_;
                        v_a_3039_ = v_a_3094_;
                        state = 11;
                        continue;
                    } else {
                        v___x_3098_ = crate::leanh::lean_box(0);
                        v___x_3099_ = lean_nat_dec_le(v___x_3096_, v___x_3096_);
                        if v___x_3099_ == 0 {
                            if v___x_3097_ == 0 {
                                crate::leanh::lean_dec(v_a_3095_);
                                v___y_3038_ = v_a_3090_;
                                v_a_3039_ = v_a_3094_;
                                state = 11;
                                continue;
                            } else {
                                v___x_3100_ = 0usize;
                                v___x_3101_ = lean_usize_of_nat(v___x_3096_);
                                v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3095_, v___x_3100_, v___x_3101_, v___x_3098_, v_a_2953_);
                                crate::leanh::lean_dec(v_a_3095_);
                                if crate::leanh::lean_obj_tag(v___x_3102_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3102_, 1);
                                    v___y_3038_ = v_a_3090_;
                                    v_a_3039_ = v_a_3094_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3094_);
                                    crate::leanh::lean_dec(v_a_3090_);
                                    crate::leanh::lean_dec_ref(v_repo_2951_);
                                    crate::leanh::lean_dec_ref(v_name_2950_);
                                    return v___x_3102_;
                                }
                            }
                        } else {
                            v___x_3103_ = 0usize;
                            v___x_3104_ = lean_usize_of_nat(v___x_3096_);
                            v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3095_, v___x_3103_, v___x_3104_, v___x_3098_, v_a_2953_);
                            crate::leanh::lean_dec(v_a_3095_);
                            if crate::leanh::lean_obj_tag(v___x_3105_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3105_, 1);
                                v___y_3038_ = v_a_3090_;
                                v_a_3039_ = v_a_3094_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_3094_);
                                crate::leanh::lean_dec(v_a_3090_);
                                crate::leanh::lean_dec_ref(v_repo_2951_);
                                crate::leanh::lean_dec_ref(v_name_2950_);
                                return v___x_3105_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3090_);
                    crate::leanh::lean_dec_ref(v_repo_2951_);
                    crate::leanh::lean_dec_ref(v_name_2950_);
                    v_a_3106_ = crate::leanh::lean_ctor_get(v___x_3093_, 1);
                    crate::leanh::lean_inc(v_a_3106_);
                    crate::leanh::lean_dec_ref_known(v___x_3093_, 2);
                    v___x_3107_ = lean_array_get_size(v_a_3106_);
                    v___x_3108_ = lean_nat_dec_lt(v___x_3087_, v___x_3107_);
                    if v___x_3108_ == 0 {
                        crate::leanh::lean_dec(v_a_3106_);
                        v___x_3109_ = crate::leanh::lean_box(0);
                        v___x_3110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3110_, 0, v___x_3109_);
                        return v___x_3110_;
                    } else {
                        v___x_3111_ = crate::leanh::lean_box(0);
                        v___x_3112_ = lean_nat_dec_le(v___x_3107_, v___x_3107_);
                        if v___x_3112_ == 0 {
                            if v___x_3108_ == 0 {
                                crate::leanh::lean_dec(v_a_3106_);
                                state = 12;
                                continue;
                            } else {
                                v___x_3113_ = 0usize;
                                v___x_3114_ = lean_usize_of_nat(v___x_3107_);
                                v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3106_, v___x_3113_, v___x_3114_, v___x_3111_, v_a_2953_);
                                crate::leanh::lean_dec(v_a_3106_);
                                if crate::leanh::lean_obj_tag(v___x_3115_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3115_, 1);
                                    state = 12;
                                    continue;
                                } else {
                                    return v___x_3115_;
                                }
                            }
                        } else {
                            v___x_3116_ = 0usize;
                            v___x_3117_ = lean_usize_of_nat(v___x_3107_);
                            v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3106_, v___x_3116_, v___x_3117_, v___x_3111_, v_a_2953_);
                            crate::leanh::lean_dec(v_a_3106_);
                            if crate::leanh::lean_obj_tag(v___x_3118_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3118_, 1);
                                state = 12;
                                continue;
                            } else {
                                return v___x_3118_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___boxed(
    mut v_name_3142_: *mut crate::leanh::LeanObject,
    mut v_repo_3143_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_a_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3147_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(
        v_name_3142_,
        v_repo_3143_,
        v_rev_x3f_3144_,
        v_a_3145_,
    );
    crate::leanh::lean_dec_ref(v_a_3145_);
    return v_res_3147_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(
    mut v_name_3149_: *mut crate::leanh::LeanObject,
    mut v_repo_3150_: *mut crate::leanh::LeanObject,
    mut v_url_3151_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: usize = 0;
    let mut v___x_3180_: usize = 0;
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3184_: u8 = 0;
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v_unused_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: usize = 0;
    let mut v___x_3191_: usize = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_unused_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: usize = 0;
    let mut v___x_3209_: usize = 0;
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: usize = 0;
    let mut v___x_3212_: usize = 0;
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: usize = 0;
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: u8 = 0;
    let mut v___x_3247_: usize = 0;
    let mut v___x_3248_: usize = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: u8 = 0;
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: usize = 0;
    let mut v___x_3279_: usize = 0;
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: u8 = 0;
    let mut v___x_3288_: usize = 0;
    let mut v___x_3289_: usize = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: usize = 0;
    let mut v___x_3292_: usize = 0;
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3261_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
                crate::leanh::lean_inc_ref(v_name_3149_);
                v___x_3262_ = lean_string_append(v_name_3149_, v___x_3261_);
                v___x_3263_ = lean_string_append(v___x_3262_, v_url_3151_);
                v___x_3264_ = 1;
                v___x_3265_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3265_, 0, v___x_3263_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3265_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3264_,
                );
                crate::leanh::lean_inc_ref(v_a_3153_);
                v___x_3266_ =
                    crate::leanh::lean_apply_2(v_a_3153_, v___x_3265_, crate::leanh::lean_box(0));
                v___x_3267_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3268_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                crate::leanh::lean_inc_ref(v_repo_3150_);
                v___x_3269_ = l_Lake_GitRepo_clone(v_url_3151_, v_repo_3150_, v___x_3268_);
                if crate::leanh::lean_obj_tag(v___x_3269_) == 0 {
                    v_a_3270_ = crate::leanh::lean_ctor_get(v___x_3269_, 1);
                    crate::leanh::lean_inc(v_a_3270_);
                    crate::leanh::lean_dec_ref_known(v___x_3269_, 2);
                    v___x_3271_ = lean_array_get_size(v_a_3270_);
                    v___x_3272_ = lean_nat_dec_lt(v___x_3267_, v___x_3271_);
                    if v___x_3272_ == 0 {
                        crate::leanh::lean_dec(v_a_3270_);
                        state = 8;
                        continue;
                    } else {
                        v___x_3273_ = crate::leanh::lean_box(0);
                        v___x_3274_ = lean_nat_dec_le(v___x_3271_, v___x_3271_);
                        if v___x_3274_ == 0 {
                            if v___x_3272_ == 0 {
                                crate::leanh::lean_dec(v_a_3270_);
                                state = 8;
                                continue;
                            } else {
                                v___x_3275_ = 0usize;
                                v___x_3276_ = lean_usize_of_nat(v___x_3271_);
                                v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3270_, v___x_3275_, v___x_3276_, v___x_3273_, v_a_3153_);
                                crate::leanh::lean_dec(v_a_3270_);
                                if crate::leanh::lean_obj_tag(v___x_3277_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3277_, 1);
                                    state = 8;
                                    continue;
                                } else {
                                    v___y_3257_ = v___x_3277_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            v___x_3278_ = 0usize;
                            v___x_3279_ = lean_usize_of_nat(v___x_3271_);
                            v___x_3280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3270_, v___x_3278_, v___x_3279_, v___x_3273_, v_a_3153_);
                            crate::leanh::lean_dec(v_a_3270_);
                            if crate::leanh::lean_obj_tag(v___x_3280_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3280_, 1);
                                state = 8;
                                continue;
                            } else {
                                v___y_3257_ = v___x_3280_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3281_ = crate::leanh::lean_ctor_get(v___x_3269_, 1);
                    crate::leanh::lean_inc(v_a_3281_);
                    crate::leanh::lean_dec_ref_known(v___x_3269_, 2);
                    v___x_3282_ = lean_array_get_size(v_a_3281_);
                    v___x_3283_ = lean_nat_dec_lt(v___x_3267_, v___x_3282_);
                    if v___x_3283_ == 0 {
                        crate::leanh::lean_dec(v_a_3281_);
                        crate::leanh::lean_dec(v_rev_x3f_3152_);
                        crate::leanh::lean_dec_ref(v_repo_3150_);
                        crate::leanh::lean_dec_ref(v_name_3149_);
                        v___x_3284_ = crate::leanh::lean_box(0);
                        v___x_3285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3285_, 0, v___x_3284_);
                        return v___x_3285_;
                    } else {
                        v___x_3286_ = crate::leanh::lean_box(0);
                        v___x_3287_ = lean_nat_dec_le(v___x_3282_, v___x_3282_);
                        if v___x_3287_ == 0 {
                            if v___x_3283_ == 0 {
                                crate::leanh::lean_dec(v_a_3281_);
                                crate::leanh::lean_dec(v_rev_x3f_3152_);
                                crate::leanh::lean_dec_ref(v_repo_3150_);
                                crate::leanh::lean_dec_ref(v_name_3149_);
                                state = 12;
                                continue;
                            } else {
                                v___x_3288_ = 0usize;
                                v___x_3289_ = lean_usize_of_nat(v___x_3282_);
                                v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3281_, v___x_3288_, v___x_3289_, v___x_3286_, v_a_3153_);
                                crate::leanh::lean_dec(v_a_3281_);
                                if crate::leanh::lean_obj_tag(v___x_3290_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3290_, 1);
                                    crate::leanh::lean_dec(v_rev_x3f_3152_);
                                    crate::leanh::lean_dec_ref(v_repo_3150_);
                                    crate::leanh::lean_dec_ref(v_name_3149_);
                                    state = 12;
                                    continue;
                                } else {
                                    v___y_3257_ = v___x_3290_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            v___x_3291_ = 0usize;
                            v___x_3292_ = lean_usize_of_nat(v___x_3282_);
                            v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3281_, v___x_3291_, v___x_3292_, v___x_3286_, v_a_3153_);
                            crate::leanh::lean_dec(v_a_3281_);
                            if crate::leanh::lean_obj_tag(v___x_3293_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3293_, 1);
                                crate::leanh::lean_dec(v_rev_x3f_3152_);
                                crate::leanh::lean_dec_ref(v_repo_3150_);
                                crate::leanh::lean_dec_ref(v_name_3149_);
                                state = 12;
                                continue;
                            } else {
                                v___y_3257_ = v___x_3293_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3156_ = crate::leanh::lean_box(0);
                v___x_3157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3157_, 0, v___x_3156_);
                return v___x_3157_;
            }
            2 => {
                v___x_3160_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
                v___x_3161_ = lean_string_append(v_name_3149_, v___x_3160_);
                v___x_3162_ = lean_string_append(v___x_3161_, v_a_3159_);
                v___x_3163_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
                v___x_3164_ = lean_string_append(v___x_3162_, v___x_3163_);
                v___x_3165_ = 1;
                v___x_3166_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3166_, 0, v___x_3164_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3166_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3165_,
                );
                crate::leanh::lean_inc_ref(v_a_3153_);
                v___x_3167_ =
                    crate::leanh::lean_apply_2(v_a_3153_, v___x_3166_, crate::leanh::lean_box(0));
                v___x_3168_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3169_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_3170_ = l_Lake_GitRepo_checkoutDetach(v_a_3159_, v_repo_3150_, v___x_3169_);
                if crate::leanh::lean_obj_tag(v___x_3170_) == 0 {
                    v_a_3171_ = crate::leanh::lean_ctor_get(v___x_3170_, 0);
                    crate::leanh::lean_inc(v_a_3171_);
                    v_a_3172_ = crate::leanh::lean_ctor_get(v___x_3170_, 1);
                    crate::leanh::lean_inc(v_a_3172_);
                    crate::leanh::lean_dec_ref_known(v___x_3170_, 2);
                    v___x_3173_ = lean_array_get_size(v_a_3172_);
                    v___x_3174_ = lean_nat_dec_lt(v___x_3168_, v___x_3173_);
                    if v___x_3174_ == 0 {
                        crate::leanh::lean_dec(v_a_3172_);
                        v___x_3175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3175_, 0, v_a_3171_);
                        return v___x_3175_;
                    } else {
                        v___x_3176_ = crate::leanh::lean_box(0);
                        v___x_3177_ = lean_nat_dec_le(v___x_3173_, v___x_3173_);
                        if v___x_3177_ == 0 {
                            if v___x_3174_ == 0 {
                                crate::leanh::lean_dec(v_a_3172_);
                                v___x_3178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3178_, 0, v_a_3171_);
                                return v___x_3178_;
                            } else {
                                v___x_3179_ = 0usize;
                                v___x_3180_ = lean_usize_of_nat(v___x_3173_);
                                v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3172_, v___x_3179_, v___x_3180_, v___x_3176_, v_a_3153_);
                                crate::leanh::lean_dec(v_a_3172_);
                                if crate::leanh::lean_obj_tag(v___x_3181_) == 0 {
                                    v_isSharedCheck_3188_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3181_)) as u8;
                                    if v_isSharedCheck_3188_ == 0 {
                                        v_unused_3189_ =
                                            crate::leanh::lean_ctor_get(v___x_3181_, 0);
                                        crate::leanh::lean_dec(v_unused_3189_);
                                        v___x_3183_ = v___x_3181_;
                                        v_isShared_3184_ = v_isSharedCheck_3188_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_3181_);
                                        v___x_3183_ = crate::leanh::lean_box(0);
                                        v_isShared_3184_ = v_isSharedCheck_3188_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3171_);
                                    return v___x_3181_;
                                }
                            }
                        } else {
                            v___x_3190_ = 0usize;
                            v___x_3191_ = lean_usize_of_nat(v___x_3173_);
                            v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3172_, v___x_3190_, v___x_3191_, v___x_3176_, v_a_3153_);
                            crate::leanh::lean_dec(v_a_3172_);
                            if crate::leanh::lean_obj_tag(v___x_3192_) == 0 {
                                v_isSharedCheck_3199_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3192_)) as u8;
                                if v_isSharedCheck_3199_ == 0 {
                                    v_unused_3200_ = crate::leanh::lean_ctor_get(v___x_3192_, 0);
                                    crate::leanh::lean_dec(v_unused_3200_);
                                    v___x_3194_ = v___x_3192_;
                                    v_isShared_3195_ = v_isSharedCheck_3199_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3192_);
                                    v___x_3194_ = crate::leanh::lean_box(0);
                                    v_isShared_3195_ = v_isSharedCheck_3199_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3171_);
                                return v___x_3192_;
                            }
                        }
                    }
                } else {
                    v_a_3201_ = crate::leanh::lean_ctor_get(v___x_3170_, 1);
                    crate::leanh::lean_inc(v_a_3201_);
                    crate::leanh::lean_dec_ref_known(v___x_3170_, 2);
                    v___x_3202_ = lean_array_get_size(v_a_3201_);
                    v___x_3203_ = lean_nat_dec_lt(v___x_3168_, v___x_3202_);
                    if v___x_3203_ == 0 {
                        crate::leanh::lean_dec(v_a_3201_);
                        v___x_3204_ = crate::leanh::lean_box(0);
                        v___x_3205_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3205_, 0, v___x_3204_);
                        return v___x_3205_;
                    } else {
                        v___x_3206_ = crate::leanh::lean_box(0);
                        v___x_3207_ = lean_nat_dec_le(v___x_3202_, v___x_3202_);
                        if v___x_3207_ == 0 {
                            if v___x_3203_ == 0 {
                                crate::leanh::lean_dec(v_a_3201_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3208_ = 0usize;
                                v___x_3209_ = lean_usize_of_nat(v___x_3202_);
                                v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3201_, v___x_3208_, v___x_3209_, v___x_3206_, v_a_3153_);
                                crate::leanh::lean_dec(v_a_3201_);
                                if crate::leanh::lean_obj_tag(v___x_3210_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3210_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    return v___x_3210_;
                                }
                            }
                        } else {
                            v___x_3211_ = 0usize;
                            v___x_3212_ = lean_usize_of_nat(v___x_3202_);
                            v___x_3213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3201_, v___x_3211_, v___x_3212_, v___x_3206_, v_a_3153_);
                            crate::leanh::lean_dec(v_a_3201_);
                            if crate::leanh::lean_obj_tag(v___x_3213_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3213_, 1);
                                state = 1;
                                continue;
                            } else {
                                return v___x_3213_;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3183_, 0, v_a_3171_);
                    v___x_3186_ = v___x_3183_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3187_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3171_);
                    v___x_3186_ = v_reuseFailAlloc_3187_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3186_;
            }
            5 => {
                if v_isShared_3195_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3194_, 0, v_a_3171_);
                    v___x_3197_ = v___x_3194_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3171_);
                    v___x_3197_ = v_reuseFailAlloc_3198_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3197_;
            }
            7 => {
                v___x_3215_ = crate::leanh::lean_box(0);
                v___x_3216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3216_, 0, v___x_3215_);
                return v___x_3216_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_rev_x3f_3152_) == 1 {
                    v_val_3218_ = crate::leanh::lean_ctor_get(v_rev_x3f_3152_, 0);
                    v_isSharedCheck_3253_ =
                        (!crate::leanh::lean_is_exclusive(v_rev_x3f_3152_)) as u8;
                    if v_isSharedCheck_3253_ == 0 {
                        v___x_3220_ = v_rev_x3f_3152_;
                        v_isShared_3221_ = v_isSharedCheck_3253_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3218_);
                        crate::leanh::lean_dec(v_rev_x3f_3152_);
                        v___x_3220_ = crate::leanh::lean_box(0);
                        v_isShared_3221_ = v_isSharedCheck_3253_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_rev_x3f_3152_);
                    crate::leanh::lean_dec_ref(v_repo_3150_);
                    crate::leanh::lean_dec_ref(v_name_3149_);
                    v___x_3254_ = crate::leanh::lean_box(0);
                    v___x_3255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3254_);
                    return v___x_3255_;
                }
            }
            9 => {
                v___x_3222_ = l_Lake_Git_defaultRemote;
                v___x_3223_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3224_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                crate::leanh::lean_inc_ref(v_repo_3150_);
                v___x_3225_ = l_Lake_GitRepo_resolveRemoteRevision(
                    v_val_3218_,
                    v___x_3222_,
                    v_repo_3150_,
                    v___x_3224_,
                );
                if crate::leanh::lean_obj_tag(v___x_3225_) == 0 {
                    crate::leanh::lean_del_object(v___x_3220_);
                    v_a_3226_ = crate::leanh::lean_ctor_get(v___x_3225_, 0);
                    crate::leanh::lean_inc(v_a_3226_);
                    v_a_3227_ = crate::leanh::lean_ctor_get(v___x_3225_, 1);
                    crate::leanh::lean_inc(v_a_3227_);
                    crate::leanh::lean_dec_ref_known(v___x_3225_, 2);
                    v___x_3228_ = lean_array_get_size(v_a_3227_);
                    v___x_3229_ = lean_nat_dec_lt(v___x_3223_, v___x_3228_);
                    if v___x_3229_ == 0 {
                        crate::leanh::lean_dec(v_a_3227_);
                        v_a_3159_ = v_a_3226_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3230_ = crate::leanh::lean_box(0);
                        v___x_3231_ = lean_nat_dec_le(v___x_3228_, v___x_3228_);
                        if v___x_3231_ == 0 {
                            if v___x_3229_ == 0 {
                                crate::leanh::lean_dec(v_a_3227_);
                                v_a_3159_ = v_a_3226_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3232_ = 0usize;
                                v___x_3233_ = lean_usize_of_nat(v___x_3228_);
                                v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3227_, v___x_3232_, v___x_3233_, v___x_3230_, v_a_3153_);
                                crate::leanh::lean_dec(v_a_3227_);
                                if crate::leanh::lean_obj_tag(v___x_3234_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3234_, 1);
                                    v_a_3159_ = v_a_3226_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3226_);
                                    crate::leanh::lean_dec_ref(v_repo_3150_);
                                    crate::leanh::lean_dec_ref(v_name_3149_);
                                    return v___x_3234_;
                                }
                            }
                        } else {
                            v___x_3235_ = 0usize;
                            v___x_3236_ = lean_usize_of_nat(v___x_3228_);
                            v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3227_, v___x_3235_, v___x_3236_, v___x_3230_, v_a_3153_);
                            crate::leanh::lean_dec(v_a_3227_);
                            if crate::leanh::lean_obj_tag(v___x_3237_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3237_, 1);
                                v_a_3159_ = v_a_3226_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_3226_);
                                crate::leanh::lean_dec_ref(v_repo_3150_);
                                crate::leanh::lean_dec_ref(v_name_3149_);
                                return v___x_3237_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_repo_3150_);
                    crate::leanh::lean_dec_ref(v_name_3149_);
                    v_a_3238_ = crate::leanh::lean_ctor_get(v___x_3225_, 1);
                    crate::leanh::lean_inc(v_a_3238_);
                    crate::leanh::lean_dec_ref_known(v___x_3225_, 2);
                    v___x_3239_ = lean_array_get_size(v_a_3238_);
                    v___x_3240_ = lean_nat_dec_lt(v___x_3223_, v___x_3239_);
                    if v___x_3240_ == 0 {
                        crate::leanh::lean_dec(v_a_3238_);
                        v___x_3241_ = crate::leanh::lean_box(0);
                        if v_isShared_3221_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3220_, 0, v___x_3241_);
                            v___x_3243_ = v___x_3220_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3244_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
                            v___x_3243_ = v_reuseFailAlloc_3244_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3220_);
                        v___x_3245_ = crate::leanh::lean_box(0);
                        v___x_3246_ = lean_nat_dec_le(v___x_3239_, v___x_3239_);
                        if v___x_3246_ == 0 {
                            if v___x_3240_ == 0 {
                                crate::leanh::lean_dec(v_a_3238_);
                                state = 7;
                                continue;
                            } else {
                                v___x_3247_ = 0usize;
                                v___x_3248_ = lean_usize_of_nat(v___x_3239_);
                                v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3238_, v___x_3247_, v___x_3248_, v___x_3245_, v_a_3153_);
                                crate::leanh::lean_dec(v_a_3238_);
                                if crate::leanh::lean_obj_tag(v___x_3249_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3249_, 1);
                                    state = 7;
                                    continue;
                                } else {
                                    return v___x_3249_;
                                }
                            }
                        } else {
                            v___x_3250_ = 0usize;
                            v___x_3251_ = lean_usize_of_nat(v___x_3239_);
                            v___x_3252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3238_, v___x_3250_, v___x_3251_, v___x_3245_, v_a_3153_);
                            crate::leanh::lean_dec(v_a_3238_);
                            if crate::leanh::lean_obj_tag(v___x_3252_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3252_, 1);
                                state = 7;
                                continue;
                            } else {
                                return v___x_3252_;
                            }
                        }
                    }
                }
            }
            10 => {
                return v___x_3243_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v___y_3257_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3257_, 1);
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_rev_x3f_3152_);
                    crate::leanh::lean_dec_ref(v_repo_3150_);
                    crate::leanh::lean_dec_ref(v_name_3149_);
                    return v___y_3257_;
                }
            }
            12 => {
                v___x_3259_ = crate::leanh::lean_box(0);
                v___x_3260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3259_);
                return v___x_3260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(
    mut v_name_3294_: *mut crate::leanh::LeanObject,
    mut v_repo_3295_: *mut crate::leanh::LeanObject,
    mut v_url_3296_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
    mut v_a_3299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3300_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(
        v_name_3294_,
        v_repo_3295_,
        v_url_3296_,
        v_rev_x3f_3297_,
        v_a_3298_,
    );
    crate::leanh::lean_dec_ref(v_a_3298_);
    return v_res_3300_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_name_3302_: *mut crate::leanh::LeanObject,
    mut v_repo_3303_: *mut crate::leanh::LeanObject,
    mut v_url_3304_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: u8 = 0;
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: usize = 0;
    let mut v___x_3332_: usize = 0;
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v_unused_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: usize = 0;
    let mut v___x_3343_: usize = 0;
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3347_: u8 = 0;
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut v_unused_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: u8 = 0;
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: usize = 0;
    let mut v___x_3361_: usize = 0;
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: usize = 0;
    let mut v___x_3364_: usize = 0;
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: u8 = 0;
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: usize = 0;
    let mut v___x_3385_: usize = 0;
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: usize = 0;
    let mut v___x_3388_: usize = 0;
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    let mut v___x_3399_: usize = 0;
    let mut v___x_3400_: usize = 0;
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: usize = 0;
    let mut v___x_3403_: usize = 0;
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: u8 = 0;
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: usize = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: usize = 0;
    let mut v___x_3431_: usize = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: usize = 0;
    let mut v___x_3441_: usize = 0;
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: usize = 0;
    let mut v___x_3444_: usize = 0;
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3413_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
                crate::leanh::lean_inc_ref(v_name_3302_);
                v___x_3414_ = lean_string_append(v_name_3302_, v___x_3413_);
                v___x_3415_ = lean_string_append(v___x_3414_, v_url_3304_);
                v___x_3416_ = 1;
                v___x_3417_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3417_, 0, v___x_3415_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3417_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3416_,
                );
                crate::leanh::lean_inc_ref(v_a_3301_);
                v___x_3418_ =
                    crate::leanh::lean_apply_2(v_a_3301_, v___x_3417_, crate::leanh::lean_box(0));
                v___x_3419_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3420_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                crate::leanh::lean_inc_ref(v_repo_3303_);
                v___x_3421_ = l_Lake_GitRepo_clone(v_url_3304_, v_repo_3303_, v___x_3420_);
                if crate::leanh::lean_obj_tag(v___x_3421_) == 0 {
                    v_a_3422_ = crate::leanh::lean_ctor_get(v___x_3421_, 1);
                    crate::leanh::lean_inc(v_a_3422_);
                    crate::leanh::lean_dec_ref_known(v___x_3421_, 2);
                    v___x_3423_ = lean_array_get_size(v_a_3422_);
                    v___x_3424_ = lean_nat_dec_lt(v___x_3419_, v___x_3423_);
                    if v___x_3424_ == 0 {
                        crate::leanh::lean_dec(v_a_3422_);
                        state = 8;
                        continue;
                    } else {
                        v___x_3425_ = crate::leanh::lean_box(0);
                        v___x_3426_ = lean_nat_dec_le(v___x_3423_, v___x_3423_);
                        if v___x_3426_ == 0 {
                            if v___x_3424_ == 0 {
                                crate::leanh::lean_dec(v_a_3422_);
                                state = 8;
                                continue;
                            } else {
                                v___x_3427_ = 0usize;
                                v___x_3428_ = lean_usize_of_nat(v___x_3423_);
                                v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3422_, v___x_3427_, v___x_3428_, v___x_3425_, v_a_3301_);
                                crate::leanh::lean_dec(v_a_3422_);
                                if crate::leanh::lean_obj_tag(v___x_3429_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3429_, 1);
                                    state = 8;
                                    continue;
                                } else {
                                    v___y_3409_ = v___x_3429_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            v___x_3430_ = 0usize;
                            v___x_3431_ = lean_usize_of_nat(v___x_3423_);
                            v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3422_, v___x_3430_, v___x_3431_, v___x_3425_, v_a_3301_);
                            crate::leanh::lean_dec(v_a_3422_);
                            if crate::leanh::lean_obj_tag(v___x_3432_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3432_, 1);
                                state = 8;
                                continue;
                            } else {
                                v___y_3409_ = v___x_3432_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3433_ = crate::leanh::lean_ctor_get(v___x_3421_, 1);
                    crate::leanh::lean_inc(v_a_3433_);
                    crate::leanh::lean_dec_ref_known(v___x_3421_, 2);
                    v___x_3434_ = lean_array_get_size(v_a_3433_);
                    v___x_3435_ = lean_nat_dec_lt(v___x_3419_, v___x_3434_);
                    if v___x_3435_ == 0 {
                        crate::leanh::lean_dec(v_a_3433_);
                        crate::leanh::lean_dec(v_rev_x3f_3305_);
                        crate::leanh::lean_dec_ref(v_repo_3303_);
                        crate::leanh::lean_dec_ref(v_name_3302_);
                        v___x_3436_ = crate::leanh::lean_box(0);
                        v___x_3437_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3437_, 0, v___x_3436_);
                        return v___x_3437_;
                    } else {
                        v___x_3438_ = crate::leanh::lean_box(0);
                        v___x_3439_ = lean_nat_dec_le(v___x_3434_, v___x_3434_);
                        if v___x_3439_ == 0 {
                            if v___x_3435_ == 0 {
                                crate::leanh::lean_dec(v_a_3433_);
                                crate::leanh::lean_dec(v_rev_x3f_3305_);
                                crate::leanh::lean_dec_ref(v_repo_3303_);
                                crate::leanh::lean_dec_ref(v_name_3302_);
                                state = 12;
                                continue;
                            } else {
                                v___x_3440_ = 0usize;
                                v___x_3441_ = lean_usize_of_nat(v___x_3434_);
                                v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3433_, v___x_3440_, v___x_3441_, v___x_3438_, v_a_3301_);
                                crate::leanh::lean_dec(v_a_3433_);
                                if crate::leanh::lean_obj_tag(v___x_3442_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3442_, 1);
                                    crate::leanh::lean_dec(v_rev_x3f_3305_);
                                    crate::leanh::lean_dec_ref(v_repo_3303_);
                                    crate::leanh::lean_dec_ref(v_name_3302_);
                                    state = 12;
                                    continue;
                                } else {
                                    v___y_3409_ = v___x_3442_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            v___x_3443_ = 0usize;
                            v___x_3444_ = lean_usize_of_nat(v___x_3434_);
                            v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3433_, v___x_3443_, v___x_3444_, v___x_3438_, v_a_3301_);
                            crate::leanh::lean_dec(v_a_3433_);
                            if crate::leanh::lean_obj_tag(v___x_3445_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3445_, 1);
                                crate::leanh::lean_dec(v_rev_x3f_3305_);
                                crate::leanh::lean_dec_ref(v_repo_3303_);
                                crate::leanh::lean_dec_ref(v_name_3302_);
                                state = 12;
                                continue;
                            } else {
                                v___y_3409_ = v___x_3445_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3308_ = crate::leanh::lean_box(0);
                v___x_3309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3308_);
                return v___x_3309_;
            }
            2 => {
                v___x_3312_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
                v___x_3313_ = lean_string_append(v_name_3302_, v___x_3312_);
                v___x_3314_ = lean_string_append(v___x_3313_, v_a_3311_);
                v___x_3315_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
                v___x_3316_ = lean_string_append(v___x_3314_, v___x_3315_);
                v___x_3317_ = 1;
                v___x_3318_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3318_, 0, v___x_3316_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3318_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3317_,
                );
                crate::leanh::lean_inc_ref(v_a_3301_);
                v___x_3319_ =
                    crate::leanh::lean_apply_2(v_a_3301_, v___x_3318_, crate::leanh::lean_box(0));
                v___x_3320_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3321_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_3322_ = l_Lake_GitRepo_checkoutDetach(v_a_3311_, v_repo_3303_, v___x_3321_);
                if crate::leanh::lean_obj_tag(v___x_3322_) == 0 {
                    v_a_3323_ = crate::leanh::lean_ctor_get(v___x_3322_, 0);
                    crate::leanh::lean_inc(v_a_3323_);
                    v_a_3324_ = crate::leanh::lean_ctor_get(v___x_3322_, 1);
                    crate::leanh::lean_inc(v_a_3324_);
                    crate::leanh::lean_dec_ref_known(v___x_3322_, 2);
                    v___x_3325_ = lean_array_get_size(v_a_3324_);
                    v___x_3326_ = lean_nat_dec_lt(v___x_3320_, v___x_3325_);
                    if v___x_3326_ == 0 {
                        crate::leanh::lean_dec(v_a_3324_);
                        v___x_3327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3327_, 0, v_a_3323_);
                        return v___x_3327_;
                    } else {
                        v___x_3328_ = crate::leanh::lean_box(0);
                        v___x_3329_ = lean_nat_dec_le(v___x_3325_, v___x_3325_);
                        if v___x_3329_ == 0 {
                            if v___x_3326_ == 0 {
                                crate::leanh::lean_dec(v_a_3324_);
                                v___x_3330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3330_, 0, v_a_3323_);
                                return v___x_3330_;
                            } else {
                                v___x_3331_ = 0usize;
                                v___x_3332_ = lean_usize_of_nat(v___x_3325_);
                                v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3324_, v___x_3331_, v___x_3332_, v___x_3328_, v_a_3301_);
                                crate::leanh::lean_dec(v_a_3324_);
                                if crate::leanh::lean_obj_tag(v___x_3333_) == 0 {
                                    v_isSharedCheck_3340_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3333_)) as u8;
                                    if v_isSharedCheck_3340_ == 0 {
                                        v_unused_3341_ =
                                            crate::leanh::lean_ctor_get(v___x_3333_, 0);
                                        crate::leanh::lean_dec(v_unused_3341_);
                                        v___x_3335_ = v___x_3333_;
                                        v_isShared_3336_ = v_isSharedCheck_3340_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_3333_);
                                        v___x_3335_ = crate::leanh::lean_box(0);
                                        v_isShared_3336_ = v_isSharedCheck_3340_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3323_);
                                    return v___x_3333_;
                                }
                            }
                        } else {
                            v___x_3342_ = 0usize;
                            v___x_3343_ = lean_usize_of_nat(v___x_3325_);
                            v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3324_, v___x_3342_, v___x_3343_, v___x_3328_, v_a_3301_);
                            crate::leanh::lean_dec(v_a_3324_);
                            if crate::leanh::lean_obj_tag(v___x_3344_) == 0 {
                                v_isSharedCheck_3351_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3344_)) as u8;
                                if v_isSharedCheck_3351_ == 0 {
                                    v_unused_3352_ = crate::leanh::lean_ctor_get(v___x_3344_, 0);
                                    crate::leanh::lean_dec(v_unused_3352_);
                                    v___x_3346_ = v___x_3344_;
                                    v_isShared_3347_ = v_isSharedCheck_3351_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3344_);
                                    v___x_3346_ = crate::leanh::lean_box(0);
                                    v_isShared_3347_ = v_isSharedCheck_3351_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3323_);
                                return v___x_3344_;
                            }
                        }
                    }
                } else {
                    v_a_3353_ = crate::leanh::lean_ctor_get(v___x_3322_, 1);
                    crate::leanh::lean_inc(v_a_3353_);
                    crate::leanh::lean_dec_ref_known(v___x_3322_, 2);
                    v___x_3354_ = lean_array_get_size(v_a_3353_);
                    v___x_3355_ = lean_nat_dec_lt(v___x_3320_, v___x_3354_);
                    if v___x_3355_ == 0 {
                        crate::leanh::lean_dec(v_a_3353_);
                        v___x_3356_ = crate::leanh::lean_box(0);
                        v___x_3357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3357_, 0, v___x_3356_);
                        return v___x_3357_;
                    } else {
                        v___x_3358_ = crate::leanh::lean_box(0);
                        v___x_3359_ = lean_nat_dec_le(v___x_3354_, v___x_3354_);
                        if v___x_3359_ == 0 {
                            if v___x_3355_ == 0 {
                                crate::leanh::lean_dec(v_a_3353_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3360_ = 0usize;
                                v___x_3361_ = lean_usize_of_nat(v___x_3354_);
                                v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3353_, v___x_3360_, v___x_3361_, v___x_3358_, v_a_3301_);
                                crate::leanh::lean_dec(v_a_3353_);
                                if crate::leanh::lean_obj_tag(v___x_3362_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3362_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    return v___x_3362_;
                                }
                            }
                        } else {
                            v___x_3363_ = 0usize;
                            v___x_3364_ = lean_usize_of_nat(v___x_3354_);
                            v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3353_, v___x_3363_, v___x_3364_, v___x_3358_, v_a_3301_);
                            crate::leanh::lean_dec(v_a_3353_);
                            if crate::leanh::lean_obj_tag(v___x_3365_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3365_, 1);
                                state = 1;
                                continue;
                            } else {
                                return v___x_3365_;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v_a_3323_);
                    v___x_3338_ = v___x_3335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3323_);
                    v___x_3338_ = v_reuseFailAlloc_3339_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3338_;
            }
            5 => {
                if v_isShared_3347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3346_, 0, v_a_3323_);
                    v___x_3349_ = v___x_3346_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3323_);
                    v___x_3349_ = v_reuseFailAlloc_3350_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3349_;
            }
            7 => {
                v___x_3367_ = crate::leanh::lean_box(0);
                v___x_3368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3368_, 0, v___x_3367_);
                return v___x_3368_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_rev_x3f_3305_) == 1 {
                    v_val_3370_ = crate::leanh::lean_ctor_get(v_rev_x3f_3305_, 0);
                    v_isSharedCheck_3405_ =
                        (!crate::leanh::lean_is_exclusive(v_rev_x3f_3305_)) as u8;
                    if v_isSharedCheck_3405_ == 0 {
                        v___x_3372_ = v_rev_x3f_3305_;
                        v_isShared_3373_ = v_isSharedCheck_3405_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3370_);
                        crate::leanh::lean_dec(v_rev_x3f_3305_);
                        v___x_3372_ = crate::leanh::lean_box(0);
                        v_isShared_3373_ = v_isSharedCheck_3405_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_rev_x3f_3305_);
                    crate::leanh::lean_dec_ref(v_repo_3303_);
                    crate::leanh::lean_dec_ref(v_name_3302_);
                    v___x_3406_ = crate::leanh::lean_box(0);
                    v___x_3407_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3407_, 0, v___x_3406_);
                    return v___x_3407_;
                }
            }
            9 => {
                v___x_3374_ = l_Lake_Git_defaultRemote;
                v___x_3375_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3376_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                crate::leanh::lean_inc_ref(v_repo_3303_);
                v___x_3377_ = l_Lake_GitRepo_resolveRemoteRevision(
                    v_val_3370_,
                    v___x_3374_,
                    v_repo_3303_,
                    v___x_3376_,
                );
                if crate::leanh::lean_obj_tag(v___x_3377_) == 0 {
                    crate::leanh::lean_del_object(v___x_3372_);
                    v_a_3378_ = crate::leanh::lean_ctor_get(v___x_3377_, 0);
                    crate::leanh::lean_inc(v_a_3378_);
                    v_a_3379_ = crate::leanh::lean_ctor_get(v___x_3377_, 1);
                    crate::leanh::lean_inc(v_a_3379_);
                    crate::leanh::lean_dec_ref_known(v___x_3377_, 2);
                    v___x_3380_ = lean_array_get_size(v_a_3379_);
                    v___x_3381_ = lean_nat_dec_lt(v___x_3375_, v___x_3380_);
                    if v___x_3381_ == 0 {
                        crate::leanh::lean_dec(v_a_3379_);
                        v_a_3311_ = v_a_3378_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3382_ = crate::leanh::lean_box(0);
                        v___x_3383_ = lean_nat_dec_le(v___x_3380_, v___x_3380_);
                        if v___x_3383_ == 0 {
                            if v___x_3381_ == 0 {
                                crate::leanh::lean_dec(v_a_3379_);
                                v_a_3311_ = v_a_3378_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3384_ = 0usize;
                                v___x_3385_ = lean_usize_of_nat(v___x_3380_);
                                v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3379_, v___x_3384_, v___x_3385_, v___x_3382_, v_a_3301_);
                                crate::leanh::lean_dec(v_a_3379_);
                                if crate::leanh::lean_obj_tag(v___x_3386_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3386_, 1);
                                    v_a_3311_ = v_a_3378_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3378_);
                                    crate::leanh::lean_dec_ref(v_repo_3303_);
                                    crate::leanh::lean_dec_ref(v_name_3302_);
                                    return v___x_3386_;
                                }
                            }
                        } else {
                            v___x_3387_ = 0usize;
                            v___x_3388_ = lean_usize_of_nat(v___x_3380_);
                            v___x_3389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3379_, v___x_3387_, v___x_3388_, v___x_3382_, v_a_3301_);
                            crate::leanh::lean_dec(v_a_3379_);
                            if crate::leanh::lean_obj_tag(v___x_3389_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3389_, 1);
                                v_a_3311_ = v_a_3378_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_3378_);
                                crate::leanh::lean_dec_ref(v_repo_3303_);
                                crate::leanh::lean_dec_ref(v_name_3302_);
                                return v___x_3389_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_repo_3303_);
                    crate::leanh::lean_dec_ref(v_name_3302_);
                    v_a_3390_ = crate::leanh::lean_ctor_get(v___x_3377_, 1);
                    crate::leanh::lean_inc(v_a_3390_);
                    crate::leanh::lean_dec_ref_known(v___x_3377_, 2);
                    v___x_3391_ = lean_array_get_size(v_a_3390_);
                    v___x_3392_ = lean_nat_dec_lt(v___x_3375_, v___x_3391_);
                    if v___x_3392_ == 0 {
                        crate::leanh::lean_dec(v_a_3390_);
                        v___x_3393_ = crate::leanh::lean_box(0);
                        if v_isShared_3373_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3372_, 0, v___x_3393_);
                            v___x_3395_ = v___x_3372_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3396_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
                            v___x_3395_ = v_reuseFailAlloc_3396_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3372_);
                        v___x_3397_ = crate::leanh::lean_box(0);
                        v___x_3398_ = lean_nat_dec_le(v___x_3391_, v___x_3391_);
                        if v___x_3398_ == 0 {
                            if v___x_3392_ == 0 {
                                crate::leanh::lean_dec(v_a_3390_);
                                state = 7;
                                continue;
                            } else {
                                v___x_3399_ = 0usize;
                                v___x_3400_ = lean_usize_of_nat(v___x_3391_);
                                v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3390_, v___x_3399_, v___x_3400_, v___x_3397_, v_a_3301_);
                                crate::leanh::lean_dec(v_a_3390_);
                                if crate::leanh::lean_obj_tag(v___x_3401_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3401_, 1);
                                    state = 7;
                                    continue;
                                } else {
                                    return v___x_3401_;
                                }
                            }
                        } else {
                            v___x_3402_ = 0usize;
                            v___x_3403_ = lean_usize_of_nat(v___x_3391_);
                            v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3390_, v___x_3402_, v___x_3403_, v___x_3397_, v_a_3301_);
                            crate::leanh::lean_dec(v_a_3390_);
                            if crate::leanh::lean_obj_tag(v___x_3404_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3404_, 1);
                                state = 7;
                                continue;
                            } else {
                                return v___x_3404_;
                            }
                        }
                    }
                }
            }
            10 => {
                return v___x_3395_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v___y_3409_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3409_, 1);
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_rev_x3f_3305_);
                    crate::leanh::lean_dec_ref(v_repo_3303_);
                    crate::leanh::lean_dec_ref(v_name_3302_);
                    return v___y_3409_;
                }
            }
            12 => {
                v___x_3411_ = crate::leanh::lean_box(0);
                v___x_3412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3412_, 0, v___x_3411_);
                return v___x_3412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_name_3447_: *mut crate::leanh::LeanObject,
    mut v_repo_3448_: *mut crate::leanh::LeanObject,
    mut v_url_3449_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3450_: *mut crate::leanh::LeanObject,
    mut v_a_3451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3452_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_3446_, v_name_3447_, v_repo_3448_, v_url_3449_, v_rev_x3f_3450_);
    crate::leanh::lean_dec_ref(v_a_3446_);
    return v_res_3452_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(
    mut v_a_3453_: *mut crate::leanh::LeanObject,
    mut v_name_3454_: *mut crate::leanh::LeanObject,
    mut v_repo_3455_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3459_: u8 = 0;
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: u8 = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3474_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: usize = 0;
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: usize = 0;
    let mut v___x_3483_: usize = 0;
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: usize = 0;
    let mut v___x_3504_: usize = 0;
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut v_unused_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: usize = 0;
    let mut v___x_3515_: usize = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3519_: u8 = 0;
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut v_unused_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: usize = 0;
    let mut v___x_3533_: usize = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: usize = 0;
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: u8 = 0;
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: u8 = 0;
    let mut v___x_3560_: usize = 0;
    let mut v___x_3561_: usize = 0;
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: usize = 0;
    let mut v___x_3564_: usize = 0;
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: usize = 0;
    let mut v___x_3574_: usize = 0;
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: usize = 0;
    let mut v___x_3577_: usize = 0;
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: u8 = 0;
    let mut v___x_3603_: usize = 0;
    let mut v___x_3604_: usize = 0;
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: usize = 0;
    let mut v___x_3607_: usize = 0;
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: u8 = 0;
    let mut v___x_3616_: usize = 0;
    let mut v___x_3617_: usize = 0;
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: usize = 0;
    let mut v___x_3620_: usize = 0;
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: usize = 0;
    let mut v___x_3627_: usize = 0;
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: usize = 0;
    let mut v___x_3630_: usize = 0;
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: u8 = 0;
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3639_: usize = 0;
    let mut v___x_3640_: usize = 0;
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: usize = 0;
    let mut v___x_3643_: usize = 0;
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3589_ = l_Lake_Git_defaultRemote;
                v___x_3590_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3591_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                crate::leanh::lean_inc_ref(v_repo_3455_);
                v___x_3592_ = l_Lake_GitRepo_findRemoteRevision(
                    v_repo_3455_,
                    v_rev_x3f_3456_,
                    v___x_3589_,
                    v___x_3591_,
                );
                if crate::leanh::lean_obj_tag(v___x_3592_) == 0 {
                    v_a_3593_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                    crate::leanh::lean_inc(v_a_3593_);
                    v_a_3594_ = crate::leanh::lean_ctor_get(v___x_3592_, 1);
                    crate::leanh::lean_inc(v_a_3594_);
                    crate::leanh::lean_dec_ref_known(v___x_3592_, 2);
                    v___x_3622_ = lean_array_get_size(v_a_3594_);
                    v___x_3623_ = lean_nat_dec_lt(v___x_3590_, v___x_3622_);
                    if v___x_3623_ == 0 {
                        crate::leanh::lean_dec(v_a_3594_);
                        state = 14;
                        continue;
                    } else {
                        v___x_3624_ = crate::leanh::lean_box(0);
                        v___x_3625_ = lean_nat_dec_le(v___x_3622_, v___x_3622_);
                        if v___x_3625_ == 0 {
                            if v___x_3623_ == 0 {
                                crate::leanh::lean_dec(v_a_3594_);
                                state = 14;
                                continue;
                            } else {
                                v___x_3626_ = 0usize;
                                v___x_3627_ = lean_usize_of_nat(v___x_3622_);
                                v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3594_, v___x_3626_, v___x_3627_, v___x_3624_, v_a_3453_);
                                crate::leanh::lean_dec(v_a_3594_);
                                if crate::leanh::lean_obj_tag(v___x_3628_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3628_, 1);
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3593_);
                                    crate::leanh::lean_dec_ref(v_repo_3455_);
                                    crate::leanh::lean_dec_ref(v_name_3454_);
                                    return v___x_3628_;
                                }
                            }
                        } else {
                            v___x_3629_ = 0usize;
                            v___x_3630_ = lean_usize_of_nat(v___x_3622_);
                            v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3594_, v___x_3629_, v___x_3630_, v___x_3624_, v_a_3453_);
                            crate::leanh::lean_dec(v_a_3594_);
                            if crate::leanh::lean_obj_tag(v___x_3631_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3631_, 1);
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_3593_);
                                crate::leanh::lean_dec_ref(v_repo_3455_);
                                crate::leanh::lean_dec_ref(v_name_3454_);
                                return v___x_3631_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_repo_3455_);
                    crate::leanh::lean_dec_ref(v_name_3454_);
                    v_a_3632_ = crate::leanh::lean_ctor_get(v___x_3592_, 1);
                    crate::leanh::lean_inc(v_a_3632_);
                    crate::leanh::lean_dec_ref_known(v___x_3592_, 2);
                    v___x_3633_ = lean_array_get_size(v_a_3632_);
                    v___x_3634_ = lean_nat_dec_lt(v___x_3590_, v___x_3633_);
                    if v___x_3634_ == 0 {
                        crate::leanh::lean_dec(v_a_3632_);
                        v___x_3635_ = crate::leanh::lean_box(0);
                        v___x_3636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3636_, 0, v___x_3635_);
                        return v___x_3636_;
                    } else {
                        v___x_3637_ = crate::leanh::lean_box(0);
                        v___x_3638_ = lean_nat_dec_le(v___x_3633_, v___x_3633_);
                        if v___x_3638_ == 0 {
                            if v___x_3634_ == 0 {
                                crate::leanh::lean_dec(v_a_3632_);
                                state = 13;
                                continue;
                            } else {
                                v___x_3639_ = 0usize;
                                v___x_3640_ = lean_usize_of_nat(v___x_3633_);
                                v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3632_, v___x_3639_, v___x_3640_, v___x_3637_, v_a_3453_);
                                crate::leanh::lean_dec(v_a_3632_);
                                if crate::leanh::lean_obj_tag(v___x_3641_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3641_, 1);
                                    state = 13;
                                    continue;
                                } else {
                                    return v___x_3641_;
                                }
                            }
                        } else {
                            v___x_3642_ = 0usize;
                            v___x_3643_ = lean_usize_of_nat(v___x_3633_);
                            v___x_3644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3632_, v___x_3642_, v___x_3643_, v___x_3637_, v_a_3453_);
                            crate::leanh::lean_dec(v_a_3632_);
                            if crate::leanh::lean_obj_tag(v___x_3644_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3644_, 1);
                                state = 13;
                                continue;
                            } else {
                                return v___x_3644_;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_a_3459_ == 0 {
                    crate::leanh::lean_dec_ref(v_repo_3455_);
                    crate::leanh::lean_dec_ref(v_name_3454_);
                    v___x_3460_ = crate::leanh::lean_box(0);
                    v___x_3461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3461_, 0, v___x_3460_);
                    return v___x_3461_;
                } else {
                    v___x_3462_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
                    v___x_3463_ = lean_string_append(v_name_3454_, v___x_3462_);
                    v___x_3464_ = lean_string_append(v___x_3463_, v_repo_3455_);
                    crate::leanh::lean_dec_ref(v_repo_3455_);
                    v___x_3465_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
                    v___x_3466_ = lean_string_append(v___x_3464_, v___x_3465_);
                    v___x_3467_ = 2;
                    v___x_3468_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3468_, 0, v___x_3466_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3468_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3467_,
                    );
                    crate::leanh::lean_inc_ref(v_a_3453_);
                    v___x_3469_ = crate::leanh::lean_apply_2(
                        v_a_3453_,
                        v___x_3468_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_3470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3470_, 0, v___x_3469_);
                    return v___x_3470_;
                }
            }
            2 => {
                v___x_3475_ = lean_array_get_size(v___y_3473_);
                v___x_3476_ = lean_nat_dec_lt(v___y_3472_, v___x_3475_);
                if v___x_3476_ == 0 {
                    v_a_3459_ = v_val_3474_;
                    state = 1;
                    continue;
                } else {
                    v___x_3477_ = crate::leanh::lean_box(0);
                    v___x_3478_ = lean_nat_dec_le(v___x_3475_, v___x_3475_);
                    if v___x_3478_ == 0 {
                        if v___x_3476_ == 0 {
                            v_a_3459_ = v_val_3474_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3479_ = 0usize;
                            v___x_3480_ = lean_usize_of_nat(v___x_3475_);
                            v___x_3481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_3473_, v___x_3479_, v___x_3480_, v___x_3477_, v_a_3453_);
                            if crate::leanh::lean_obj_tag(v___x_3481_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3481_, 1);
                                v_a_3459_ = v_val_3474_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_repo_3455_);
                                crate::leanh::lean_dec_ref(v_name_3454_);
                                return v___x_3481_;
                            }
                        }
                    } else {
                        v___x_3482_ = 0usize;
                        v___x_3483_ = lean_usize_of_nat(v___x_3475_);
                        v___x_3484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_3473_, v___x_3482_, v___x_3483_, v___x_3477_, v_a_3453_);
                        if crate::leanh::lean_obj_tag(v___x_3484_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3484_, 1);
                            v_a_3459_ = v_val_3474_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_repo_3455_);
                            crate::leanh::lean_dec_ref(v_name_3454_);
                            return v___x_3484_;
                        }
                    }
                }
            }
            3 => {
                v___x_3486_ = crate::leanh::lean_box(0);
                v___x_3487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3487_, 0, v___x_3486_);
                return v___x_3487_;
            }
            4 => {
                v___x_3489_ = crate::leanh::lean_box(0);
                v___x_3490_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3490_, 0, v___x_3489_);
                return v___x_3490_;
            }
            5 => {
                v___x_3492_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3493_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_3494_ = l_Lake_GitRepo_clean(v_repo_3455_, v___x_3493_);
                if crate::leanh::lean_obj_tag(v___x_3494_) == 0 {
                    v_a_3495_ = crate::leanh::lean_ctor_get(v___x_3494_, 0);
                    crate::leanh::lean_inc(v_a_3495_);
                    v_a_3496_ = crate::leanh::lean_ctor_get(v___x_3494_, 1);
                    crate::leanh::lean_inc(v_a_3496_);
                    crate::leanh::lean_dec_ref_known(v___x_3494_, 2);
                    v___x_3497_ = lean_array_get_size(v_a_3496_);
                    v___x_3498_ = lean_nat_dec_lt(v___x_3492_, v___x_3497_);
                    if v___x_3498_ == 0 {
                        crate::leanh::lean_dec(v_a_3496_);
                        v___x_3499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3499_, 0, v_a_3495_);
                        return v___x_3499_;
                    } else {
                        v___x_3500_ = crate::leanh::lean_box(0);
                        v___x_3501_ = lean_nat_dec_le(v___x_3497_, v___x_3497_);
                        if v___x_3501_ == 0 {
                            if v___x_3498_ == 0 {
                                crate::leanh::lean_dec(v_a_3496_);
                                v___x_3502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3502_, 0, v_a_3495_);
                                return v___x_3502_;
                            } else {
                                v___x_3503_ = 0usize;
                                v___x_3504_ = lean_usize_of_nat(v___x_3497_);
                                v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3496_, v___x_3503_, v___x_3504_, v___x_3500_, v_a_3453_);
                                crate::leanh::lean_dec(v_a_3496_);
                                if crate::leanh::lean_obj_tag(v___x_3505_) == 0 {
                                    v_isSharedCheck_3512_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3505_)) as u8;
                                    if v_isSharedCheck_3512_ == 0 {
                                        v_unused_3513_ =
                                            crate::leanh::lean_ctor_get(v___x_3505_, 0);
                                        crate::leanh::lean_dec(v_unused_3513_);
                                        v___x_3507_ = v___x_3505_;
                                        v_isShared_3508_ = v_isSharedCheck_3512_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_3505_);
                                        v___x_3507_ = crate::leanh::lean_box(0);
                                        v_isShared_3508_ = v_isSharedCheck_3512_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3495_);
                                    return v___x_3505_;
                                }
                            }
                        } else {
                            v___x_3514_ = 0usize;
                            v___x_3515_ = lean_usize_of_nat(v___x_3497_);
                            v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3496_, v___x_3514_, v___x_3515_, v___x_3500_, v_a_3453_);
                            crate::leanh::lean_dec(v_a_3496_);
                            if crate::leanh::lean_obj_tag(v___x_3516_) == 0 {
                                v_isSharedCheck_3523_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3516_)) as u8;
                                if v_isSharedCheck_3523_ == 0 {
                                    v_unused_3524_ = crate::leanh::lean_ctor_get(v___x_3516_, 0);
                                    crate::leanh::lean_dec(v_unused_3524_);
                                    v___x_3518_ = v___x_3516_;
                                    v_isShared_3519_ = v_isSharedCheck_3523_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3516_);
                                    v___x_3518_ = crate::leanh::lean_box(0);
                                    v_isShared_3519_ = v_isSharedCheck_3523_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3495_);
                                return v___x_3516_;
                            }
                        }
                    }
                } else {
                    v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3494_, 1);
                    crate::leanh::lean_inc(v_a_3525_);
                    crate::leanh::lean_dec_ref_known(v___x_3494_, 2);
                    v___x_3526_ = lean_array_get_size(v_a_3525_);
                    v___x_3527_ = lean_nat_dec_lt(v___x_3492_, v___x_3526_);
                    if v___x_3527_ == 0 {
                        crate::leanh::lean_dec(v_a_3525_);
                        v___x_3528_ = crate::leanh::lean_box(0);
                        v___x_3529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3529_, 0, v___x_3528_);
                        return v___x_3529_;
                    } else {
                        v___x_3530_ = crate::leanh::lean_box(0);
                        v___x_3531_ = lean_nat_dec_le(v___x_3526_, v___x_3526_);
                        if v___x_3531_ == 0 {
                            if v___x_3527_ == 0 {
                                crate::leanh::lean_dec(v_a_3525_);
                                state = 4;
                                continue;
                            } else {
                                v___x_3532_ = 0usize;
                                v___x_3533_ = lean_usize_of_nat(v___x_3526_);
                                v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3525_, v___x_3532_, v___x_3533_, v___x_3530_, v_a_3453_);
                                crate::leanh::lean_dec(v_a_3525_);
                                if crate::leanh::lean_obj_tag(v___x_3534_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3534_, 1);
                                    state = 4;
                                    continue;
                                } else {
                                    return v___x_3534_;
                                }
                            }
                        } else {
                            v___x_3535_ = 0usize;
                            v___x_3536_ = lean_usize_of_nat(v___x_3526_);
                            v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3525_, v___x_3535_, v___x_3536_, v___x_3530_, v_a_3453_);
                            crate::leanh::lean_dec(v_a_3525_);
                            if crate::leanh::lean_obj_tag(v___x_3537_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3537_, 1);
                                state = 4;
                                continue;
                            } else {
                                return v___x_3537_;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_3508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3507_, 0, v_a_3495_);
                    v___x_3510_ = v___x_3507_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3495_);
                    v___x_3510_ = v_reuseFailAlloc_3511_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3510_;
            }
            8 => {
                if v_isShared_3519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3518_, 0, v_a_3495_);
                    v___x_3521_ = v___x_3518_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3495_);
                    v___x_3521_ = v_reuseFailAlloc_3522_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3521_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v___y_3539_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3539_, 1);
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_repo_3455_);
                    return v___y_3539_;
                }
            }
            11 => {
                v___x_3543_ = lean_string_dec_eq(v_a_3542_, v___y_3541_);
                crate::leanh::lean_dec_ref(v_a_3542_);
                if v___x_3543_ == 0 {
                    v___x_3544_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
                    v___x_3545_ = lean_string_append(v_name_3454_, v___x_3544_);
                    v___x_3546_ = lean_string_append(v___x_3545_, v___y_3541_);
                    v___x_3547_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
                    v___x_3548_ = lean_string_append(v___x_3546_, v___x_3547_);
                    v___x_3549_ = 1;
                    v___x_3550_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3550_, 0, v___x_3548_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3550_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3549_,
                    );
                    crate::leanh::lean_inc_ref(v_a_3453_);
                    v___x_3551_ = crate::leanh::lean_apply_2(
                        v_a_3453_,
                        v___x_3550_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_3552_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3553_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    crate::leanh::lean_inc_ref(v_repo_3455_);
                    v___x_3554_ =
                        l_Lake_GitRepo_checkoutDetach(v___y_3541_, v_repo_3455_, v___x_3553_);
                    if crate::leanh::lean_obj_tag(v___x_3554_) == 0 {
                        v_a_3555_ = crate::leanh::lean_ctor_get(v___x_3554_, 1);
                        crate::leanh::lean_inc(v_a_3555_);
                        crate::leanh::lean_dec_ref_known(v___x_3554_, 2);
                        v___x_3556_ = lean_array_get_size(v_a_3555_);
                        v___x_3557_ = lean_nat_dec_lt(v___x_3552_, v___x_3556_);
                        if v___x_3557_ == 0 {
                            crate::leanh::lean_dec(v_a_3555_);
                            state = 5;
                            continue;
                        } else {
                            v___x_3558_ = crate::leanh::lean_box(0);
                            v___x_3559_ = lean_nat_dec_le(v___x_3556_, v___x_3556_);
                            if v___x_3559_ == 0 {
                                if v___x_3557_ == 0 {
                                    crate::leanh::lean_dec(v_a_3555_);
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_3560_ = 0usize;
                                    v___x_3561_ = lean_usize_of_nat(v___x_3556_);
                                    v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3555_, v___x_3560_, v___x_3561_, v___x_3558_, v_a_3453_);
                                    crate::leanh::lean_dec(v_a_3555_);
                                    if crate::leanh::lean_obj_tag(v___x_3562_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3562_, 1);
                                        state = 5;
                                        continue;
                                    } else {
                                        v___y_3539_ = v___x_3562_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3563_ = 0usize;
                                v___x_3564_ = lean_usize_of_nat(v___x_3556_);
                                v___x_3565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3555_, v___x_3563_, v___x_3564_, v___x_3558_, v_a_3453_);
                                crate::leanh::lean_dec(v_a_3555_);
                                if crate::leanh::lean_obj_tag(v___x_3565_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3565_, 1);
                                    state = 5;
                                    continue;
                                } else {
                                    v___y_3539_ = v___x_3565_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_3566_ = crate::leanh::lean_ctor_get(v___x_3554_, 1);
                        crate::leanh::lean_inc(v_a_3566_);
                        crate::leanh::lean_dec_ref_known(v___x_3554_, 2);
                        v___x_3567_ = lean_array_get_size(v_a_3566_);
                        v___x_3568_ = lean_nat_dec_lt(v___x_3552_, v___x_3567_);
                        if v___x_3568_ == 0 {
                            crate::leanh::lean_dec(v_a_3566_);
                            crate::leanh::lean_dec_ref(v_repo_3455_);
                            v___x_3569_ = crate::leanh::lean_box(0);
                            v___x_3570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3570_, 0, v___x_3569_);
                            return v___x_3570_;
                        } else {
                            v___x_3571_ = crate::leanh::lean_box(0);
                            v___x_3572_ = lean_nat_dec_le(v___x_3567_, v___x_3567_);
                            if v___x_3572_ == 0 {
                                if v___x_3568_ == 0 {
                                    crate::leanh::lean_dec(v_a_3566_);
                                    crate::leanh::lean_dec_ref(v_repo_3455_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3573_ = 0usize;
                                    v___x_3574_ = lean_usize_of_nat(v___x_3567_);
                                    v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3566_, v___x_3573_, v___x_3574_, v___x_3571_, v_a_3453_);
                                    crate::leanh::lean_dec(v_a_3566_);
                                    if crate::leanh::lean_obj_tag(v___x_3575_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3575_, 1);
                                        crate::leanh::lean_dec_ref(v_repo_3455_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___y_3539_ = v___x_3575_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3576_ = 0usize;
                                v___x_3577_ = lean_usize_of_nat(v___x_3567_);
                                v___x_3578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3566_, v___x_3576_, v___x_3577_, v___x_3571_, v_a_3453_);
                                crate::leanh::lean_dec(v_a_3566_);
                                if crate::leanh::lean_obj_tag(v___x_3578_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3578_, 1);
                                    crate::leanh::lean_dec_ref(v_repo_3455_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___y_3539_ = v___x_3578_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3541_);
                    crate::leanh::lean_inc_ref(v_repo_3455_);
                    v___x_3579_ = l_Lake_GitRepo_hasNoDiff(v_repo_3455_);
                    v___x_3580_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3581_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    if v___x_3579_ == 0 {
                        v___y_3472_ = v___x_3580_;
                        v___y_3473_ = v___x_3581_;
                        v_val_3474_ = v___x_3543_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3582_ = 0;
                        v___y_3472_ = v___x_3580_;
                        v___y_3473_ = v___x_3581_;
                        v_val_3474_ = v___x_3582_;
                        state = 2;
                        continue;
                    }
                }
            }
            12 => {
                v___x_3584_ = crate::leanh::lean_box(0);
                v___x_3585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3585_, 0, v___x_3584_);
                return v___x_3585_;
            }
            13 => {
                v___x_3587_ = crate::leanh::lean_box(0);
                v___x_3588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3588_, 0, v___x_3587_);
                return v___x_3588_;
            }
            14 => {
                crate::leanh::lean_inc_ref(v_repo_3455_);
                v___x_3596_ = l_Lake_GitRepo_getHeadRevision(v_repo_3455_, v___x_3591_);
                if crate::leanh::lean_obj_tag(v___x_3596_) == 0 {
                    v_a_3597_ = crate::leanh::lean_ctor_get(v___x_3596_, 0);
                    crate::leanh::lean_inc(v_a_3597_);
                    v_a_3598_ = crate::leanh::lean_ctor_get(v___x_3596_, 1);
                    crate::leanh::lean_inc(v_a_3598_);
                    crate::leanh::lean_dec_ref_known(v___x_3596_, 2);
                    v___x_3599_ = lean_array_get_size(v_a_3598_);
                    v___x_3600_ = lean_nat_dec_lt(v___x_3590_, v___x_3599_);
                    if v___x_3600_ == 0 {
                        crate::leanh::lean_dec(v_a_3598_);
                        v___y_3541_ = v_a_3593_;
                        v_a_3542_ = v_a_3597_;
                        state = 11;
                        continue;
                    } else {
                        v___x_3601_ = crate::leanh::lean_box(0);
                        v___x_3602_ = lean_nat_dec_le(v___x_3599_, v___x_3599_);
                        if v___x_3602_ == 0 {
                            if v___x_3600_ == 0 {
                                crate::leanh::lean_dec(v_a_3598_);
                                v___y_3541_ = v_a_3593_;
                                v_a_3542_ = v_a_3597_;
                                state = 11;
                                continue;
                            } else {
                                v___x_3603_ = 0usize;
                                v___x_3604_ = lean_usize_of_nat(v___x_3599_);
                                v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3598_, v___x_3603_, v___x_3604_, v___x_3601_, v_a_3453_);
                                crate::leanh::lean_dec(v_a_3598_);
                                if crate::leanh::lean_obj_tag(v___x_3605_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3605_, 1);
                                    v___y_3541_ = v_a_3593_;
                                    v_a_3542_ = v_a_3597_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3597_);
                                    crate::leanh::lean_dec(v_a_3593_);
                                    crate::leanh::lean_dec_ref(v_repo_3455_);
                                    crate::leanh::lean_dec_ref(v_name_3454_);
                                    return v___x_3605_;
                                }
                            }
                        } else {
                            v___x_3606_ = 0usize;
                            v___x_3607_ = lean_usize_of_nat(v___x_3599_);
                            v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3598_, v___x_3606_, v___x_3607_, v___x_3601_, v_a_3453_);
                            crate::leanh::lean_dec(v_a_3598_);
                            if crate::leanh::lean_obj_tag(v___x_3608_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3608_, 1);
                                v___y_3541_ = v_a_3593_;
                                v_a_3542_ = v_a_3597_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_3597_);
                                crate::leanh::lean_dec(v_a_3593_);
                                crate::leanh::lean_dec_ref(v_repo_3455_);
                                crate::leanh::lean_dec_ref(v_name_3454_);
                                return v___x_3608_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3593_);
                    crate::leanh::lean_dec_ref(v_repo_3455_);
                    crate::leanh::lean_dec_ref(v_name_3454_);
                    v_a_3609_ = crate::leanh::lean_ctor_get(v___x_3596_, 1);
                    crate::leanh::lean_inc(v_a_3609_);
                    crate::leanh::lean_dec_ref_known(v___x_3596_, 2);
                    v___x_3610_ = lean_array_get_size(v_a_3609_);
                    v___x_3611_ = lean_nat_dec_lt(v___x_3590_, v___x_3610_);
                    if v___x_3611_ == 0 {
                        crate::leanh::lean_dec(v_a_3609_);
                        v___x_3612_ = crate::leanh::lean_box(0);
                        v___x_3613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3612_);
                        return v___x_3613_;
                    } else {
                        v___x_3614_ = crate::leanh::lean_box(0);
                        v___x_3615_ = lean_nat_dec_le(v___x_3610_, v___x_3610_);
                        if v___x_3615_ == 0 {
                            if v___x_3611_ == 0 {
                                crate::leanh::lean_dec(v_a_3609_);
                                state = 12;
                                continue;
                            } else {
                                v___x_3616_ = 0usize;
                                v___x_3617_ = lean_usize_of_nat(v___x_3610_);
                                v___x_3618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3609_, v___x_3616_, v___x_3617_, v___x_3614_, v_a_3453_);
                                crate::leanh::lean_dec(v_a_3609_);
                                if crate::leanh::lean_obj_tag(v___x_3618_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3618_, 1);
                                    state = 12;
                                    continue;
                                } else {
                                    return v___x_3618_;
                                }
                            }
                        } else {
                            v___x_3619_ = 0usize;
                            v___x_3620_ = lean_usize_of_nat(v___x_3610_);
                            v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3609_, v___x_3619_, v___x_3620_, v___x_3614_, v_a_3453_);
                            crate::leanh::lean_dec(v_a_3609_);
                            if crate::leanh::lean_obj_tag(v___x_3621_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3621_, 1);
                                state = 12;
                                continue;
                            } else {
                                return v___x_3621_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1___boxed(
    mut v_a_3645_: *mut crate::leanh::LeanObject,
    mut v_name_3646_: *mut crate::leanh::LeanObject,
    mut v_repo_3647_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3648_: *mut crate::leanh::LeanObject,
    mut v_a_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3645_, v_name_3646_, v_repo_3647_, v_rev_x3f_3648_);
    crate::leanh::lean_dec_ref(v_a_3645_);
    return v_res_3650_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3655_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
    v___x_3656_ = lean_array_get_size(v___x_3655_);
    return v___x_3656_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5() -> u8 {
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: u8 = 0;
    v___x_3657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once
        ),
        _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4,
    );
    v___x_3658_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3659_ = lean_nat_dec_lt(v___x_3658_, v___x_3657_);
    return v___x_3659_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6() -> u8 {
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: u8 = 0;
    v___x_3660_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once
        ),
        _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4,
    );
    v___x_3661_ = lean_nat_dec_le(v___x_3660_, v___x_3660_);
    return v___x_3661_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7() -> usize {
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: usize = 0;
    v___x_3662_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once
        ),
        _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4,
    );
    v___x_3663_ = lean_usize_of_nat(v___x_3662_);
    return v___x_3663_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(
    mut v_name_3664_: *mut crate::leanh::LeanObject,
    mut v_repo_3665_: *mut crate::leanh::LeanObject,
    mut v_url_3666_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3667_: *mut crate::leanh::LeanObject,
    mut v_a_3668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3671_: u8 = 0;
    let mut v___x_3672_: u8 = 0;
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3710_: u8 = 0;
    let mut v___x_3711_: u8 = 0;
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: u8 = 0;
    let mut v___x_3714_: usize = 0;
    let mut v___x_3715_: usize = 0;
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: usize = 0;
    let mut v___x_3718_: usize = 0;
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3706_ = l_Lake_Git_defaultRemote;
                crate::leanh::lean_inc_ref(v_repo_3665_);
                v___x_3707_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_3706_, v_repo_3665_);
                v___x_3708_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                if crate::leanh::lean_obj_tag(v___x_3707_) == 1 {
                    v_val_3720_ = crate::leanh::lean_ctor_get(v___x_3707_, 0);
                    crate::leanh::lean_inc(v_val_3720_);
                    crate::leanh::lean_dec_ref_known(v___x_3707_, 1);
                    v___x_3721_ = lean_string_dec_eq(v_val_3720_, v_url_3666_);
                    if v___x_3721_ == 0 {
                        v___x_3722_ = lean_io_realpath(v_val_3720_);
                        if crate::leanh::lean_obj_tag(v___x_3722_) == 0 {
                            v_a_3723_ = crate::leanh::lean_ctor_get(v___x_3722_, 0);
                            crate::leanh::lean_inc(v_a_3723_);
                            crate::leanh::lean_dec_ref_known(v___x_3722_, 1);
                            crate::leanh::lean_inc_ref(v_url_3666_);
                            v___x_3724_ = lean_io_realpath(v_url_3666_);
                            if crate::leanh::lean_obj_tag(v___x_3724_) == 0 {
                                v_a_3725_ = crate::leanh::lean_ctor_get(v___x_3724_, 0);
                                crate::leanh::lean_inc(v_a_3725_);
                                crate::leanh::lean_dec_ref_known(v___x_3724_, 1);
                                v___x_3726_ = lean_string_dec_eq(v_a_3723_, v_a_3725_);
                                crate::leanh::lean_dec(v_a_3725_);
                                crate::leanh::lean_dec(v_a_3723_);
                                v_val_3710_ = v___x_3726_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_3724_, 1);
                                crate::leanh::lean_dec(v_a_3723_);
                                v_val_3710_ = v___x_3721_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3722_, 1);
                            v_val_3710_ = v___x_3721_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3720_);
                        v_val_3710_ = v___x_3721_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3707_);
                    v___x_3727_ = 0;
                    v_val_3710_ = v___x_3727_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                if v_a_3671_ == 0 {
                    v___x_3672_ = l_System_Platform_isWindows;
                    if v___x_3672_ == 0 {
                        v___x_3673_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
                        crate::leanh::lean_inc_ref(v_name_3664_);
                        v___x_3674_ = lean_string_append(v_name_3664_, v___x_3673_);
                        v___x_3675_ = lean_string_append(v___x_3674_, v_repo_3665_);
                        v___x_3676_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
                        v___x_3677_ = lean_string_append(v___x_3675_, v___x_3676_);
                        v___x_3678_ = 1;
                        v___x_3679_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3679_, 0, v___x_3677_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3679_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_3678_,
                        );
                        crate::leanh::lean_inc_ref(v_a_3668_);
                        v___x_3680_ = crate::leanh::lean_apply_2(
                            v_a_3668_,
                            v___x_3679_,
                            crate::leanh::lean_box(0),
                        );
                        v___x_3681_ = l_IO_FS_removeDirAll(v_repo_3665_);
                        if crate::leanh::lean_obj_tag(v___x_3681_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3681_, 1);
                            v___x_3682_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_3668_, v_name_3664_, v_repo_3665_, v_url_3666_, v_rev_x3f_3667_);
                            return v___x_3682_;
                        } else {
                            crate::leanh::lean_dec(v_rev_x3f_3667_);
                            crate::leanh::lean_dec_ref(v_url_3666_);
                            crate::leanh::lean_dec_ref(v_repo_3665_);
                            crate::leanh::lean_dec_ref(v_name_3664_);
                            v_a_3683_ = crate::leanh::lean_ctor_get(v___x_3681_, 0);
                            v_isSharedCheck_3695_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3681_)) as u8;
                            if v_isSharedCheck_3695_ == 0 {
                                v___x_3685_ = v___x_3681_;
                                v_isShared_3686_ = v_isSharedCheck_3695_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3683_);
                                crate::leanh::lean_dec(v___x_3681_);
                                v___x_3685_ = crate::leanh::lean_box(0);
                                v_isShared_3686_ = v_isSharedCheck_3695_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_url_3666_);
                        v___x_3696_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
                        crate::leanh::lean_inc_ref(v_name_3664_);
                        v___x_3697_ = lean_string_append(v_name_3664_, v___x_3696_);
                        v___x_3698_ = lean_string_append(v___x_3697_, v_repo_3665_);
                        v___x_3699_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
                        v___x_3700_ = lean_string_append(v___x_3698_, v___x_3699_);
                        v___x_3701_ = 1;
                        v___x_3702_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3702_, 0, v___x_3700_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3702_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_3701_,
                        );
                        crate::leanh::lean_inc_ref(v_a_3668_);
                        v___x_3703_ = crate::leanh::lean_apply_2(
                            v_a_3668_,
                            v___x_3702_,
                            crate::leanh::lean_box(0),
                        );
                        v___x_3704_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3668_, v_name_3664_, v_repo_3665_, v_rev_x3f_3667_);
                        return v___x_3704_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_url_3666_);
                    v___x_3705_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3668_, v_name_3664_, v_repo_3665_, v_rev_x3f_3667_);
                    return v___x_3705_;
                }
            }
            2 => {
                v___x_3687_ = lean_io_error_to_string(v_a_3683_);
                v___x_3688_ = 3;
                v___x_3689_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3689_, 0, v___x_3687_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3689_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3688_,
                );
                crate::leanh::lean_inc_ref(v_a_3668_);
                v___x_3690_ =
                    crate::leanh::lean_apply_2(v_a_3668_, v___x_3689_, crate::leanh::lean_box(0));
                v___x_3691_ = crate::leanh::lean_box(0);
                if v_isShared_3686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3685_, 0, v___x_3691_);
                    v___x_3693_ = v___x_3685_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
                    v___x_3693_ = v_reuseFailAlloc_3694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3693_;
            }
            4 => {
                v___x_3711_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once
                    ),
                    _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5,
                );
                if v___x_3711_ == 0 {
                    v_a_3671_ = v_val_3710_;
                    state = 1;
                    continue;
                } else {
                    v___x_3712_ = crate::leanh::lean_box(0);
                    v___x_3713_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_3713_ == 0 {
                        if v___x_3711_ == 0 {
                            v_a_3671_ = v_val_3710_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3714_ = 0usize;
                            v___x_3715_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_3716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3708_, v___x_3714_, v___x_3715_, v___x_3712_, v_a_3668_);
                            if crate::leanh::lean_obj_tag(v___x_3716_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3716_, 1);
                                v_a_3671_ = v_val_3710_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_rev_x3f_3667_);
                                crate::leanh::lean_dec_ref(v_url_3666_);
                                crate::leanh::lean_dec_ref(v_repo_3665_);
                                crate::leanh::lean_dec_ref(v_name_3664_);
                                return v___x_3716_;
                            }
                        }
                    } else {
                        v___x_3717_ = 0usize;
                        v___x_3718_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3708_, v___x_3717_, v___x_3718_, v___x_3712_, v_a_3668_);
                        if crate::leanh::lean_obj_tag(v___x_3719_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3719_, 1);
                            v_a_3671_ = v_val_3710_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_rev_x3f_3667_);
                            crate::leanh::lean_dec_ref(v_url_3666_);
                            crate::leanh::lean_dec_ref(v_repo_3665_);
                            crate::leanh::lean_dec_ref(v_name_3664_);
                            return v___x_3719_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___boxed(
    mut v_name_3728_: *mut crate::leanh::LeanObject,
    mut v_repo_3729_: *mut crate::leanh::LeanObject,
    mut v_url_3730_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3731_: *mut crate::leanh::LeanObject,
    mut v_a_3732_: *mut crate::leanh::LeanObject,
    mut v_a_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3734_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(
        v_name_3728_,
        v_repo_3729_,
        v_url_3730_,
        v_rev_x3f_3731_,
        v_a_3732_,
    );
    crate::leanh::lean_dec_ref(v_a_3732_);
    return v_res_3734_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_name_3736_: *mut crate::leanh::LeanObject,
    mut v_repo_3737_: *mut crate::leanh::LeanObject,
    mut v_url_3738_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3742_: u8 = 0;
    let mut v___x_3743_: u8 = 0;
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: u8 = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: u8 = 0;
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3781_: u8 = 0;
    let mut v___x_3782_: u8 = 0;
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: usize = 0;
    let mut v___x_3786_: usize = 0;
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: usize = 0;
    let mut v___x_3789_: usize = 0;
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: u8 = 0;
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3777_ = l_Lake_Git_defaultRemote;
                crate::leanh::lean_inc_ref(v_repo_3737_);
                v___x_3778_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_3777_, v_repo_3737_);
                v___x_3779_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                if crate::leanh::lean_obj_tag(v___x_3778_) == 1 {
                    v_val_3791_ = crate::leanh::lean_ctor_get(v___x_3778_, 0);
                    crate::leanh::lean_inc(v_val_3791_);
                    crate::leanh::lean_dec_ref_known(v___x_3778_, 1);
                    v___x_3792_ = lean_string_dec_eq(v_val_3791_, v_url_3738_);
                    if v___x_3792_ == 0 {
                        v___x_3793_ = lean_io_realpath(v_val_3791_);
                        if crate::leanh::lean_obj_tag(v___x_3793_) == 0 {
                            v_a_3794_ = crate::leanh::lean_ctor_get(v___x_3793_, 0);
                            crate::leanh::lean_inc(v_a_3794_);
                            crate::leanh::lean_dec_ref_known(v___x_3793_, 1);
                            crate::leanh::lean_inc_ref(v_url_3738_);
                            v___x_3795_ = lean_io_realpath(v_url_3738_);
                            if crate::leanh::lean_obj_tag(v___x_3795_) == 0 {
                                v_a_3796_ = crate::leanh::lean_ctor_get(v___x_3795_, 0);
                                crate::leanh::lean_inc(v_a_3796_);
                                crate::leanh::lean_dec_ref_known(v___x_3795_, 1);
                                v___x_3797_ = lean_string_dec_eq(v_a_3794_, v_a_3796_);
                                crate::leanh::lean_dec(v_a_3796_);
                                crate::leanh::lean_dec(v_a_3794_);
                                v_val_3781_ = v___x_3797_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_3795_, 1);
                                crate::leanh::lean_dec(v_a_3794_);
                                v_val_3781_ = v___x_3792_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3793_, 1);
                            v_val_3781_ = v___x_3792_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3791_);
                        v_val_3781_ = v___x_3792_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3778_);
                    v___x_3798_ = 0;
                    v_val_3781_ = v___x_3798_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                if v_a_3742_ == 0 {
                    v___x_3743_ = l_System_Platform_isWindows;
                    if v___x_3743_ == 0 {
                        v___x_3744_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0;
                        crate::leanh::lean_inc_ref(v_name_3736_);
                        v___x_3745_ = lean_string_append(v_name_3736_, v___x_3744_);
                        v___x_3746_ = lean_string_append(v___x_3745_, v_repo_3737_);
                        v___x_3747_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
                        v___x_3748_ = lean_string_append(v___x_3746_, v___x_3747_);
                        v___x_3749_ = 1;
                        v___x_3750_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3750_, 0, v___x_3748_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3750_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_3749_,
                        );
                        crate::leanh::lean_inc_ref(v_a_3735_);
                        v___x_3751_ = crate::leanh::lean_apply_2(
                            v_a_3735_,
                            v___x_3750_,
                            crate::leanh::lean_box(0),
                        );
                        v___x_3752_ = l_IO_FS_removeDirAll(v_repo_3737_);
                        if crate::leanh::lean_obj_tag(v___x_3752_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3752_, 1);
                            v___x_3753_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_3735_, v_name_3736_, v_repo_3737_, v_url_3738_, v_rev_x3f_3739_);
                            return v___x_3753_;
                        } else {
                            crate::leanh::lean_dec(v_rev_x3f_3739_);
                            crate::leanh::lean_dec_ref(v_url_3738_);
                            crate::leanh::lean_dec_ref(v_repo_3737_);
                            crate::leanh::lean_dec_ref(v_name_3736_);
                            v_a_3754_ = crate::leanh::lean_ctor_get(v___x_3752_, 0);
                            v_isSharedCheck_3766_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3752_)) as u8;
                            if v_isSharedCheck_3766_ == 0 {
                                v___x_3756_ = v___x_3752_;
                                v_isShared_3757_ = v_isSharedCheck_3766_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3754_);
                                crate::leanh::lean_dec(v___x_3752_);
                                v___x_3756_ = crate::leanh::lean_box(0);
                                v_isShared_3757_ = v_isSharedCheck_3766_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_url_3738_);
                        v___x_3767_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
                        crate::leanh::lean_inc_ref(v_name_3736_);
                        v___x_3768_ = lean_string_append(v_name_3736_, v___x_3767_);
                        v___x_3769_ = lean_string_append(v___x_3768_, v_repo_3737_);
                        v___x_3770_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
                        v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
                        v___x_3772_ = 1;
                        v___x_3773_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3773_, 0, v___x_3771_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3773_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_3772_,
                        );
                        crate::leanh::lean_inc_ref(v_a_3735_);
                        v___x_3774_ = crate::leanh::lean_apply_2(
                            v_a_3735_,
                            v___x_3773_,
                            crate::leanh::lean_box(0),
                        );
                        v___x_3775_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3735_, v_name_3736_, v_repo_3737_, v_rev_x3f_3739_);
                        return v___x_3775_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_url_3738_);
                    v___x_3776_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3735_, v_name_3736_, v_repo_3737_, v_rev_x3f_3739_);
                    return v___x_3776_;
                }
            }
            2 => {
                v___x_3758_ = lean_io_error_to_string(v_a_3754_);
                v___x_3759_ = 3;
                v___x_3760_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3760_, 0, v___x_3758_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3759_,
                );
                crate::leanh::lean_inc_ref(v_a_3735_);
                v___x_3761_ =
                    crate::leanh::lean_apply_2(v_a_3735_, v___x_3760_, crate::leanh::lean_box(0));
                v___x_3762_ = crate::leanh::lean_box(0);
                if v_isShared_3757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3756_, 0, v___x_3762_);
                    v___x_3764_ = v___x_3756_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
                    v___x_3764_ = v_reuseFailAlloc_3765_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3764_;
            }
            4 => {
                v___x_3782_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once
                    ),
                    _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5,
                );
                if v___x_3782_ == 0 {
                    v_a_3742_ = v_val_3781_;
                    state = 1;
                    continue;
                } else {
                    v___x_3783_ = crate::leanh::lean_box(0);
                    v___x_3784_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_3784_ == 0 {
                        if v___x_3782_ == 0 {
                            v_a_3742_ = v_val_3781_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3785_ = 0usize;
                            v___x_3786_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3779_, v___x_3785_, v___x_3786_, v___x_3783_, v_a_3735_);
                            if crate::leanh::lean_obj_tag(v___x_3787_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3787_, 1);
                                v_a_3742_ = v_val_3781_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_rev_x3f_3739_);
                                crate::leanh::lean_dec_ref(v_url_3738_);
                                crate::leanh::lean_dec_ref(v_repo_3737_);
                                crate::leanh::lean_dec_ref(v_name_3736_);
                                return v___x_3787_;
                            }
                        }
                    } else {
                        v___x_3788_ = 0usize;
                        v___x_3789_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_3790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3779_, v___x_3788_, v___x_3789_, v___x_3783_, v_a_3735_);
                        if crate::leanh::lean_obj_tag(v___x_3790_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3790_, 1);
                            v_a_3742_ = v_val_3781_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_rev_x3f_3739_);
                            crate::leanh::lean_dec_ref(v_url_3738_);
                            crate::leanh::lean_dec_ref(v_repo_3737_);
                            crate::leanh::lean_dec_ref(v_name_3736_);
                            return v___x_3790_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0___boxed(
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_name_3800_: *mut crate::leanh::LeanObject,
    mut v_repo_3801_: *mut crate::leanh::LeanObject,
    mut v_url_3802_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3805_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_3799_, v_name_3800_, v_repo_3801_, v_url_3802_, v_rev_x3f_3803_);
    crate::leanh::lean_dec_ref(v_a_3799_);
    return v_res_3805_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(
    mut v_name_3806_: *mut crate::leanh::LeanObject,
    mut v_repo_3807_: *mut crate::leanh::LeanObject,
    mut v_url_3808_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: u8 = 0;
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: u8 = 0;
    let mut v___x_3820_: usize = 0;
    let mut v___x_3821_: usize = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: usize = 0;
    let mut v___x_3824_: usize = 0;
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3812_ = l_System_FilePath_isDir(v_repo_3807_);
                v___x_3816_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_3817_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once
                    ),
                    _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5,
                );
                if v___x_3817_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3818_ = crate::leanh::lean_box(0);
                    v___x_3819_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_3819_ == 0 {
                        if v___x_3817_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3820_ = 0usize;
                            v___x_3821_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3816_, v___x_3820_, v___x_3821_, v___x_3818_, v_a_3810_);
                            if crate::leanh::lean_obj_tag(v___x_3822_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3822_, 1);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_rev_x3f_3809_);
                                crate::leanh::lean_dec_ref(v_url_3808_);
                                crate::leanh::lean_dec_ref(v_repo_3807_);
                                crate::leanh::lean_dec_ref(v_name_3806_);
                                return v___x_3822_;
                            }
                        }
                    } else {
                        v___x_3823_ = 0usize;
                        v___x_3824_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3816_, v___x_3823_, v___x_3824_, v___x_3818_, v_a_3810_);
                        if crate::leanh::lean_obj_tag(v___x_3825_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3825_, 1);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_rev_x3f_3809_);
                            crate::leanh::lean_dec_ref(v_url_3808_);
                            crate::leanh::lean_dec_ref(v_repo_3807_);
                            crate::leanh::lean_dec_ref(v_name_3806_);
                            return v___x_3825_;
                        }
                    }
                }
            }
            1 => {
                if v___x_3812_ == 0 {
                    v___x_3814_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_3810_, v_name_3806_, v_repo_3807_, v_url_3808_, v_rev_x3f_3809_);
                    return v___x_3814_;
                } else {
                    v___x_3815_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_3810_, v_name_3806_, v_repo_3807_, v_url_3808_, v_rev_x3f_3809_);
                    return v___x_3815_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___boxed(
    mut v_name_3826_: *mut crate::leanh::LeanObject,
    mut v_repo_3827_: *mut crate::leanh::LeanObject,
    mut v_url_3828_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_3829_: *mut crate::leanh::LeanObject,
    mut v_a_3830_: *mut crate::leanh::LeanObject,
    mut v_a_3831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3832_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(
        v_name_3826_,
        v_repo_3827_,
        v_url_3828_,
        v_rev_x3f_3829_,
        v_a_3830_,
    );
    crate::leanh::lean_dec_ref(v_a_3830_);
    return v_res_3832_;
}
pub unsafe fn _init_l_Lake_instInhabitedMaterializedDep_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l_Lake_instInhabitedPackageEntry_default;
    v___x_3840_ = l_Lake_instInhabitedMaterializedDep_default___closed__3;
    v___x_3841_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
    v___x_3842_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3842_, 0, v___x_3841_);
    crate::leanh::lean_ctor_set(v___x_3842_, 1, v___x_3841_);
    crate::leanh::lean_ctor_set(v___x_3842_, 2, v___x_3841_);
    crate::leanh::lean_ctor_set(v___x_3842_, 3, v___x_3840_);
    crate::leanh::lean_ctor_set(v___x_3842_, 4, v___x_3839_);
    return v___x_3842_;
}
pub unsafe fn _init_l_Lake_instInhabitedMaterializedDep_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3843_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedMaterializedDep_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedMaterializedDep_default___closed__4_once),
        _init_l_Lake_instInhabitedMaterializedDep_default___closed__4,
    );
    return v___x_3843_;
}
pub unsafe fn _init_l_Lake_instInhabitedMaterializedDep() -> *mut crate::leanh::LeanObject {
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ = l_Lake_instInhabitedMaterializedDep_default;
    return v___x_3844_;
}
pub unsafe fn l_Lake_MaterializedDep_name(
    mut v_self_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_manifestEntry_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifestEntry_3846_ = crate::leanh::lean_ctor_get(v_self_3845_, 4);
    v_name_3847_ = crate::leanh::lean_ctor_get(v_manifestEntry_3846_, 0);
    crate::leanh::lean_inc(v_name_3847_);
    return v_name_3847_;
}
pub unsafe fn l_Lake_MaterializedDep_name___boxed(
    mut v_self_3848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3849_ = l_Lake_MaterializedDep_name(v_self_3848_);
    crate::leanh::lean_dec_ref(v_self_3848_);
    return v_res_3849_;
}
pub unsafe fn l_Lake_MaterializedDep_prettyName(
    mut v_self_3850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_manifestEntry_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifestEntry_3851_ = crate::leanh::lean_ctor_get(v_self_3850_, 4);
    crate::leanh::lean_inc_ref(v_manifestEntry_3851_);
    crate::leanh::lean_dec_ref(v_self_3850_);
    v_name_3852_ = crate::leanh::lean_ctor_get(v_manifestEntry_3851_, 0);
    crate::leanh::lean_inc(v_name_3852_);
    crate::leanh::lean_dec_ref(v_manifestEntry_3851_);
    v___x_3853_ = 0;
    v___x_3854_ = l_Lean_Name_toString(v_name_3852_, v___x_3853_);
    return v___x_3854_;
}
pub unsafe fn l_Lake_MaterializedDep_scope(
    mut v_self_3855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_manifestEntry_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifestEntry_3856_ = crate::leanh::lean_ctor_get(v_self_3855_, 4);
    v_scope_3857_ = crate::leanh::lean_ctor_get(v_manifestEntry_3856_, 1);
    crate::leanh::lean_inc_ref(v_scope_3857_);
    return v_scope_3857_;
}
pub unsafe fn l_Lake_MaterializedDep_scope___boxed(
    mut v_self_3858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Lake_MaterializedDep_scope(v_self_3858_);
    crate::leanh::lean_dec_ref(v_self_3858_);
    return v_res_3859_;
}
pub unsafe fn l_Lake_MaterializedDep_relManifestFile_x3f(
    mut v_self_3860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_manifestEntry_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifestEntry_3861_ = crate::leanh::lean_ctor_get(v_self_3860_, 4);
    v_manifestFile_x3f_3862_ = crate::leanh::lean_ctor_get(v_manifestEntry_3861_, 3);
    crate::leanh::lean_inc(v_manifestFile_x3f_3862_);
    return v_manifestFile_x3f_3862_;
}
pub unsafe fn l_Lake_MaterializedDep_relManifestFile_x3f___boxed(
    mut v_self_3863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3864_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_3863_);
    crate::leanh::lean_dec_ref(v_self_3863_);
    return v_res_3864_;
}
pub unsafe fn l_Lake_MaterializedDep_relManifestFile(
    mut v_self_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_manifestEntry_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifestEntry_3866_ = crate::leanh::lean_ctor_get(v_self_3865_, 4);
    v_manifestFile_x3f_3867_ = crate::leanh::lean_ctor_get(v_manifestEntry_3866_, 3);
    if crate::leanh::lean_obj_tag(v_manifestFile_x3f_3867_) == 0 {
        let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3868_ = l_Lake_defaultManifestFile;
        return v___x_3868_;
    } else {
        let mut v_val_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3869_ = crate::leanh::lean_ctor_get(v_manifestFile_x3f_3867_, 0);
        crate::leanh::lean_inc(v_val_3869_);
        return v_val_3869_;
    }
}
pub unsafe fn l_Lake_MaterializedDep_relManifestFile___boxed(
    mut v_self_3870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3871_ = l_Lake_MaterializedDep_relManifestFile(v_self_3870_);
    crate::leanh::lean_dec_ref(v_self_3870_);
    return v_res_3871_;
}
pub unsafe fn l_Lake_MaterializedDep_manifestFile(
    mut v_self_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_manifestEntry_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifestEntry_3873_ = crate::leanh::lean_ctor_get(v_self_3872_, 4);
    v_manifestFile_x3f_3874_ = crate::leanh::lean_ctor_get(v_manifestEntry_3873_, 3);
    if crate::leanh::lean_obj_tag(v_manifestFile_x3f_3874_) == 0 {
        let mut v_pkgDir_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pkgDir_3875_ = crate::leanh::lean_ctor_get(v_self_3872_, 0);
        crate::leanh::lean_inc_ref(v_pkgDir_3875_);
        crate::leanh::lean_dec_ref(v_self_3872_);
        v___x_3876_ = l_Lake_defaultManifestFile;
        v___x_3877_ = l_Lake_joinRelative(v_pkgDir_3875_, v___x_3876_);
        return v___x_3877_;
    } else {
        let mut v_pkgDir_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_manifestFile_x3f_3874_);
        v_pkgDir_3878_ = crate::leanh::lean_ctor_get(v_self_3872_, 0);
        crate::leanh::lean_inc_ref(v_pkgDir_3878_);
        crate::leanh::lean_dec_ref(v_self_3872_);
        v_val_3879_ = crate::leanh::lean_ctor_get(v_manifestFile_x3f_3874_, 0);
        crate::leanh::lean_inc(v_val_3879_);
        crate::leanh::lean_dec_ref_known(v_manifestFile_x3f_3874_, 1);
        v___x_3880_ = l_Lake_joinRelative(v_pkgDir_3878_, v_val_3879_);
        return v___x_3880_;
    }
}
pub unsafe fn l_Lake_MaterializedDep_relConfigFile(
    mut v_self_3881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_manifestEntry_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifestEntry_3882_ = crate::leanh::lean_ctor_get(v_self_3881_, 4);
    v_configFile_3883_ = crate::leanh::lean_ctor_get(v_manifestEntry_3882_, 2);
    crate::leanh::lean_inc_ref(v_configFile_3883_);
    return v_configFile_3883_;
}
pub unsafe fn l_Lake_MaterializedDep_relConfigFile___boxed(
    mut v_self_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Lake_MaterializedDep_relConfigFile(v_self_3884_);
    crate::leanh::lean_dec_ref(v_self_3884_);
    return v_res_3885_;
}
pub unsafe fn l_Lake_MaterializedDep_configFile(
    mut v_self_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_manifestEntry_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifestEntry_3887_ = crate::leanh::lean_ctor_get(v_self_3886_, 4);
    crate::leanh::lean_inc_ref(v_manifestEntry_3887_);
    v_pkgDir_3888_ = crate::leanh::lean_ctor_get(v_self_3886_, 0);
    crate::leanh::lean_inc_ref(v_pkgDir_3888_);
    crate::leanh::lean_dec_ref(v_self_3886_);
    v_configFile_3889_ = crate::leanh::lean_ctor_get(v_manifestEntry_3887_, 2);
    crate::leanh::lean_inc_ref(v_configFile_3889_);
    crate::leanh::lean_dec_ref(v_manifestEntry_3887_);
    v___x_3890_ = l_Lake_joinRelative(v_pkgDir_3888_, v_configFile_3889_);
    return v___x_3890_;
}
pub unsafe fn l_Lake_MaterializedDep_fixedToolchain(
    mut v_self_3891_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_manifest_x3f_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_manifest_x3f_3892_ = crate::leanh::lean_ctor_get(v_self_3891_, 3);
    if crate::leanh::lean_obj_tag(v_manifest_x3f_3892_) == 1 {
        let mut v_a_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fixedToolchain_3894_: u8 = 0;
        v_a_3893_ = crate::leanh::lean_ctor_get(v_manifest_x3f_3892_, 0);
        v_fixedToolchain_3894_ = crate::leanh::lean_ctor_get_uint8(
            v_a_3893_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        return v_fixedToolchain_3894_;
    } else {
        let mut v___x_3895_: u8 = 0;
        v___x_3895_ = 0;
        return v___x_3895_;
    }
}
pub unsafe fn l_Lake_MaterializedDep_fixedToolchain___boxed(
    mut v_self_3896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3897_: u8 = 0;
    let mut v_r_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3897_ = l_Lake_MaterializedDep_fixedToolchain(v_self_3896_);
    crate::leanh::lean_dec_ref(v_self_3896_);
    v_r_3898_ = crate::leanh::lean_box((v_res_3897_) as usize);
    return v_r_3898_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(
    mut v_x_3899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3899_) {
        0 => {
            let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3900_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3900_;
        }
        1 => {
            let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3901_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3901_;
        }
        _ => {
            let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3902_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3902_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(
    mut v_x_3903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3904_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(v_x_3903_);
    crate::leanh::lean_dec(v_x_3903_);
    return v_res_3904_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
    mut v_t_3905_: *mut crate::leanh::LeanObject,
    mut v_k_3906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3905_) == 0 {
        return v_k_3906_;
    } else {
        let mut v_rev_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_rev_3907_ = crate::leanh::lean_ctor_get(v_t_3905_, 0);
        crate::leanh::lean_inc_ref(v_rev_3907_);
        crate::leanh::lean_dec(v_t_3905_);
        v___x_3908_ = crate::leanh::lean_apply_1(v_k_3906_, v_rev_3907_);
        return v___x_3908_;
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(
    mut v_motive_3909_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3910_: *mut crate::leanh::LeanObject,
    mut v_t_3911_: *mut crate::leanh::LeanObject,
    mut v_h_3912_: *mut crate::leanh::LeanObject,
    mut v_k_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ =
        l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_3911_, v_k_3913_);
    return v___x_3914_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(
    mut v_motive_3915_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3916_: *mut crate::leanh::LeanObject,
    mut v_t_3917_: *mut crate::leanh::LeanObject,
    mut v_h_3918_: *mut crate::leanh::LeanObject,
    mut v_k_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3920_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(
        v_motive_3915_,
        v_ctorIdx_3916_,
        v_t_3917_,
        v_h_3918_,
        v_k_3919_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3916_);
    return v_res_3920_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(
    mut v_t_3921_: *mut crate::leanh::LeanObject,
    mut v_none_3922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3923_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3921_,
        v_none_3922_,
    );
    return v___x_3923_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(
    mut v_motive_3924_: *mut crate::leanh::LeanObject,
    mut v_t_3925_: *mut crate::leanh::LeanObject,
    mut v_h_3926_: *mut crate::leanh::LeanObject,
    mut v_none_3927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3928_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3925_,
        v_none_3927_,
    );
    return v___x_3928_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(
    mut v_t_3929_: *mut crate::leanh::LeanObject,
    mut v_git_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3931_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3929_,
        v_git_3930_,
    );
    return v___x_3931_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(
    mut v_motive_3932_: *mut crate::leanh::LeanObject,
    mut v_t_3933_: *mut crate::leanh::LeanObject,
    mut v_h_3934_: *mut crate::leanh::LeanObject,
    mut v_git_3935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3936_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3933_,
        v_git_3935_,
    );
    return v___x_3936_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(
    mut v_t_3937_: *mut crate::leanh::LeanObject,
    mut v_ver_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3937_,
        v_ver_3938_,
    );
    return v___x_3939_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(
    mut v_motive_3940_: *mut crate::leanh::LeanObject,
    mut v_t_3941_: *mut crate::leanh::LeanObject,
    mut v_h_3942_: *mut crate::leanh::LeanObject,
    mut v_ver_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3944_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3941_,
        v_ver_3943_,
    );
    return v___x_3944_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(
    mut v_scope_3953_: *mut crate::leanh::LeanObject,
    mut v_name_3954_: *mut crate::leanh::LeanObject,
    mut v_ver_3955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rev_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v_ver_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v_toString_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_ver_3955_) {
                0 => {
                    v___x_3979_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                    v_fst_3957_ = v___x_3979_;
                    v_snd_3958_ = v___x_3979_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_rev_3980_ = crate::leanh::lean_ctor_get(v_ver_3955_, 0);
                    v_isSharedCheck_3995_ = (!crate::leanh::lean_is_exclusive(v_ver_3955_)) as u8;
                    if v_isSharedCheck_3995_ == 0 {
                        v___x_3982_ = v_ver_3955_;
                        v_isShared_3983_ = v_isSharedCheck_3995_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rev_3980_);
                        crate::leanh::lean_dec(v_ver_3955_);
                        v___x_3982_ = crate::leanh::lean_box(0);
                        v_isShared_3983_ = v_isSharedCheck_3995_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v_ver_3996_ = crate::leanh::lean_ctor_get(v_ver_3955_, 0);
                    v_isSharedCheck_4012_ = (!crate::leanh::lean_is_exclusive(v_ver_3955_)) as u8;
                    if v_isSharedCheck_4012_ == 0 {
                        v___x_3998_ = v_ver_3955_;
                        v_isShared_3999_ = v_isSharedCheck_4012_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ver_3996_);
                        crate::leanh::lean_dec(v_ver_3955_);
                        v___x_3998_ = crate::leanh::lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4012_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3959_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                crate::leanh::lean_inc_ref(v_scope_3953_);
                v___x_3960_ = lean_string_append(v_scope_3953_, v___x_3959_);
                v___x_3961_ = lean_string_append(v___x_3960_, v_name_3954_);
                v___x_3962_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1;
                v___x_3963_ = lean_string_append(v___x_3961_, v___x_3962_);
                v___x_3964_ = lean_string_append(v___x_3963_, v_scope_3953_);
                v___x_3965_ = lean_string_append(v___x_3964_, v___x_3959_);
                v___x_3966_ = lean_string_append(v___x_3965_, v_name_3954_);
                v___x_3967_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2;
                v___x_3968_ = lean_string_append(v___x_3966_, v___x_3967_);
                v___x_3969_ = lean_string_append(v___x_3968_, v_fst_3957_);
                crate::leanh::lean_dec_ref(v_fst_3957_);
                v___x_3970_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3;
                v___x_3971_ = lean_string_append(v___x_3969_, v___x_3970_);
                v___x_3972_ = lean_string_append(v___x_3971_, v_scope_3953_);
                crate::leanh::lean_dec_ref(v_scope_3953_);
                v___x_3973_ = lean_string_append(v___x_3972_, v___x_3959_);
                v___x_3974_ = lean_string_append(v___x_3973_, v_name_3954_);
                v___x_3975_ = lean_string_append(v___x_3974_, v___x_3967_);
                v___x_3976_ = lean_string_append(v___x_3975_, v_snd_3958_);
                crate::leanh::lean_dec_ref(v_snd_3958_);
                v___x_3977_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4;
                v___x_3978_ = lean_string_append(v___x_3976_, v___x_3977_);
                return v___x_3978_;
            }
            2 => {
                v___x_3984_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
                v___x_3985_ = l_String_quote(v_rev_3980_);
                if v_isShared_3983_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3982_, 3);
                    crate::leanh::lean_ctor_set(v___x_3982_, 0, v___x_3985_);
                    v___x_3987_ = v___x_3982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3985_);
                    v___x_3987_ = v_reuseFailAlloc_3994_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3988_ = l_Std_Format_defWidth;
                v___x_3989_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3990_ =
                    l_Std_Format_pretty(v___x_3987_, v___x_3988_, v___x_3989_, v___x_3989_);
                v___x_3991_ = lean_string_append(v___x_3984_, v___x_3990_);
                v___x_3992_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
                v___x_3993_ = lean_string_append(v___x_3992_, v___x_3990_);
                crate::leanh::lean_dec_ref(v___x_3990_);
                v_fst_3957_ = v___x_3991_;
                v_snd_3958_ = v___x_3993_;
                state = 1;
                continue;
            }
            4 => {
                v_toString_4000_ = crate::leanh::lean_ctor_get(v_ver_3996_, 0);
                crate::leanh::lean_inc_ref(v_toString_4000_);
                crate::leanh::lean_dec_ref(v_ver_3996_);
                v___x_4001_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
                v___x_4002_ = l_String_quote(v_toString_4000_);
                if v_isShared_3999_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3998_, 3);
                    crate::leanh::lean_ctor_set(v___x_3998_, 0, v___x_4002_);
                    v___x_4004_ = v___x_3998_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4002_);
                    v___x_4004_ = v_reuseFailAlloc_4011_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4005_ = l_Std_Format_defWidth;
                v___x_4006_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4007_ =
                    l_Std_Format_pretty(v___x_4004_, v___x_4005_, v___x_4006_, v___x_4006_);
                v___x_4008_ = lean_string_append(v___x_4001_, v___x_4007_);
                v___x_4009_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
                v___x_4010_ = lean_string_append(v___x_4009_, v___x_4007_);
                crate::leanh::lean_dec_ref(v___x_4007_);
                v_fst_3957_ = v___x_4008_;
                v_snd_3958_ = v___x_4010_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___boxed(
    mut v_scope_4013_: *mut crate::leanh::LeanObject,
    mut v_name_4014_: *mut crate::leanh::LeanObject,
    mut v_ver_4015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4016_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(
        v_scope_4013_,
        v_name_4014_,
        v_ver_4015_,
    );
    crate::leanh::lean_dec_ref(v_name_4014_);
    return v_res_4016_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(
    mut v_x_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
    mut v___y_4019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___y_4019_);
    v___x_4021_ = crate::leanh::lean_apply_2(v___y_4019_, v___y_4018_, crate::leanh::lean_box(0));
    v___x_4022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4022_, 0, v___x_4021_);
    return v___x_4022_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(
    mut v_x_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4027_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(
        v_x_4023_,
        v___y_4024_,
        v___y_4025_,
    );
    crate::leanh::lean_dec_ref(v___y_4025_);
    return v_res_4027_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4028_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_4028_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4029_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once
        ),
        _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0,
    );
    v___x_4030_ = l_ReaderT_instMonad___redArg(v___x_4029_);
    return v___x_4030_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(
    mut v_dep_4033_: *mut crate::leanh::LeanObject,
    mut v_inherited_4034_: u8,
    mut v_wsDir_4035_: *mut crate::leanh::LeanObject,
    mut v_name_4036_: *mut crate::leanh::LeanObject,
    mut v_relPkgDir_4037_: *mut crate::leanh::LeanObject,
    mut v_remoteUrl_4038_: *mut crate::leanh::LeanObject,
    mut v_src_4039_: *mut crate::leanh::LeanObject,
    mut v_a_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut v_unused_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: usize = 0;
    let mut v___x_4076_: usize = 0;
    let mut v___x_2388__overap_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4082_: u8 = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v___x_4087_: usize = 0;
    let mut v___x_4088_: usize = 0;
    let mut v___x_2398__overap_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4094_: u8 = 0;
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_a_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4110_: u8 = 0;
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v_a_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4122_: u8 = 0;
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: u8 = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: u8 = 0;
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    let mut v___x_4138_: usize = 0;
    let mut v___x_4139_: usize = 0;
    let mut v___x_2450__overap_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut v___x_4150_: usize = 0;
    let mut v___x_4151_: usize = 0;
    let mut v___x_2460__overap_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4157_: u8 = 0;
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4161_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: u8 = 0;
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_relPkgDir_4037_);
                v_pkgDir_4061_ = l_Lake_joinRelative(v_wsDir_4035_, v_relPkgDir_4037_);
                v___x_4062_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once), _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
                crate::leanh::lean_inc_ref(v_pkgDir_4061_);
                v___x_4063_ = l_Lake_resolvePath(v_pkgDir_4061_);
                v___f_4064_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2;
                v___x_4131_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4132_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4162_ = lean_string_utf8_byte_size(v___x_4063_);
                v___x_4163_ = lean_nat_dec_eq(v___x_4162_, v___x_4131_);
                if v___x_4163_ == 0 {
                    v___x_4164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4164_, 0, v___x_4063_);
                    v_val_4134_ = v___x_4164_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_4063_);
                    v___x_4165_ = crate::leanh::lean_box(0);
                    v_val_4134_ = v___x_4165_;
                    state = 14;
                    continue;
                }
            }
            1 => {
                v_name_4045_ = crate::leanh::lean_ctor_get(v_dep_4033_, 0);
                v_scope_4046_ = crate::leanh::lean_ctor_get(v_dep_4033_, 1);
                v_isSharedCheck_4057_ = (!crate::leanh::lean_is_exclusive(v_dep_4033_)) as u8;
                if v_isSharedCheck_4057_ == 0 {
                    v_unused_4058_ = crate::leanh::lean_ctor_get(v_dep_4033_, 4);
                    crate::leanh::lean_dec(v_unused_4058_);
                    v_unused_4059_ = crate::leanh::lean_ctor_get(v_dep_4033_, 3);
                    crate::leanh::lean_dec(v_unused_4059_);
                    v_unused_4060_ = crate::leanh::lean_ctor_get(v_dep_4033_, 2);
                    crate::leanh::lean_dec(v_unused_4060_);
                    v___x_4048_ = v_dep_4033_;
                    v_isShared_4049_ = v_isSharedCheck_4057_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_scope_4046_);
                    crate::leanh::lean_inc(v_name_4045_);
                    crate::leanh::lean_dec(v_dep_4033_);
                    v___x_4048_ = crate::leanh::lean_box(0);
                    v_isShared_4049_ = v_isSharedCheck_4057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4050_ = l_Lake_defaultConfigFile;
                v___x_4051_ = crate::leanh::lean_box(0);
                v___x_4052_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4052_, 0, v_name_4045_);
                crate::leanh::lean_ctor_set(v___x_4052_, 1, v_scope_4046_);
                crate::leanh::lean_ctor_set(v___x_4052_, 2, v___x_4050_);
                crate::leanh::lean_ctor_set(v___x_4052_, 3, v___x_4051_);
                crate::leanh::lean_ctor_set(v___x_4052_, 4, v_src_4039_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4052_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_inherited_4034_,
                );
                if v_isShared_4049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4048_, 4, v___x_4052_);
                    crate::leanh::lean_ctor_set(v___x_4048_, 3, v_a_4044_);
                    crate::leanh::lean_ctor_set(v___x_4048_, 2, v_remoteUrl_4038_);
                    crate::leanh::lean_ctor_set(v___x_4048_, 1, v_relPkgDir_4037_);
                    crate::leanh::lean_ctor_set(v___x_4048_, 0, v___y_4043_);
                    v___x_4054_ = v___x_4048_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___y_4043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_relPkgDir_4037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_remoteUrl_4038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 3, v_a_4044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 4, v___x_4052_);
                    v___x_4054_ = v_reuseFailAlloc_4056_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4055_, 0, v___x_4054_);
                return v___x_4055_;
            }
            4 => {
                v___x_4071_ = lean_array_get_size(v___y_4067_);
                v___x_4072_ = lean_nat_dec_lt(v___y_4066_, v___x_4071_);
                if v___x_4072_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4069_);
                    v___y_4043_ = v___y_4068_;
                    v_a_4044_ = v_val_4070_;
                    state = 1;
                    continue;
                } else {
                    v___x_4073_ = crate::leanh::lean_box(0);
                    v___x_4074_ = lean_nat_dec_le(v___x_4071_, v___x_4071_);
                    if v___x_4074_ == 0 {
                        if v___x_4072_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_4069_);
                            v___y_4043_ = v___y_4068_;
                            v_a_4044_ = v_val_4070_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4075_ = 0usize;
                            v___x_4076_ = lean_usize_of_nat(v___x_4071_);
                            crate::leanh::lean_inc_ref(v___y_4067_);
                            v___x_2388__overap_4077_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___y_4069_,
                                    v___f_4064_,
                                    v___y_4067_,
                                    v___x_4075_,
                                    v___x_4076_,
                                    v___x_4073_,
                                );
                            crate::leanh::lean_inc_ref(v_a_4040_);
                            v___x_4078_ = crate::leanh::lean_apply_2(
                                v___x_2388__overap_4077_,
                                v_a_4040_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_4078_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4078_, 1);
                                v___y_4043_ = v___y_4068_;
                                v_a_4044_ = v_val_4070_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_val_4070_);
                                crate::leanh::lean_dec_ref(v___y_4068_);
                                crate::leanh::lean_dec_ref(v_src_4039_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_4038_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_4037_);
                                crate::leanh::lean_dec_ref(v_dep_4033_);
                                v_a_4079_ = crate::leanh::lean_ctor_get(v___x_4078_, 0);
                                v_isSharedCheck_4086_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4078_)) as u8;
                                if v_isSharedCheck_4086_ == 0 {
                                    v___x_4081_ = v___x_4078_;
                                    v_isShared_4082_ = v_isSharedCheck_4086_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4079_);
                                    crate::leanh::lean_dec(v___x_4078_);
                                    v___x_4081_ = crate::leanh::lean_box(0);
                                    v_isShared_4082_ = v_isSharedCheck_4086_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4087_ = 0usize;
                        v___x_4088_ = lean_usize_of_nat(v___x_4071_);
                        crate::leanh::lean_inc_ref(v___y_4067_);
                        v___x_2398__overap_4089_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___y_4069_,
                                v___f_4064_,
                                v___y_4067_,
                                v___x_4087_,
                                v___x_4088_,
                                v___x_4073_,
                            );
                        crate::leanh::lean_inc_ref(v_a_4040_);
                        v___x_4090_ = crate::leanh::lean_apply_2(
                            v___x_2398__overap_4089_,
                            v_a_4040_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4090_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4090_, 1);
                            v___y_4043_ = v___y_4068_;
                            v_a_4044_ = v_val_4070_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_val_4070_);
                            crate::leanh::lean_dec_ref(v___y_4068_);
                            crate::leanh::lean_dec_ref(v_src_4039_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_4038_);
                            crate::leanh::lean_dec_ref(v_relPkgDir_4037_);
                            crate::leanh::lean_dec_ref(v_dep_4033_);
                            v_a_4091_ = crate::leanh::lean_ctor_get(v___x_4090_, 0);
                            v_isSharedCheck_4098_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4090_)) as u8;
                            if v_isSharedCheck_4098_ == 0 {
                                v___x_4093_ = v___x_4090_;
                                v_isShared_4094_ = v_isSharedCheck_4098_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4091_);
                                crate::leanh::lean_dec(v___x_4090_);
                                v___x_4093_ = crate::leanh::lean_box(0);
                                v_isShared_4094_ = v_isSharedCheck_4098_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                if v_isShared_4082_ == 0 {
                    v___x_4084_ = v___x_4081_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
                    v___x_4084_ = v_reuseFailAlloc_4085_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4084_;
            }
            7 => {
                if v_isShared_4094_ == 0 {
                    v___x_4096_ = v___x_4093_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
                    v___x_4096_ = v_reuseFailAlloc_4097_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4096_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_4100_) == 1 {
                    crate::leanh::lean_dec_ref(v_pkgDir_4061_);
                    crate::leanh::lean_dec_ref(v_name_4036_);
                    v_val_4101_ = crate::leanh::lean_ctor_get(v_a_4100_, 0);
                    crate::leanh::lean_inc_n(v_val_4101_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_4100_, 1);
                    v___x_4102_ = l_Lake_defaultManifestFile;
                    v___x_4103_ = l_Lake_joinRelative(v_val_4101_, v___x_4102_);
                    v___x_4104_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4105_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_4106_ = l_Lake_Manifest_load(v___x_4103_);
                    if crate::leanh::lean_obj_tag(v___x_4106_) == 0 {
                        v_a_4107_ = crate::leanh::lean_ctor_get(v___x_4106_, 0);
                        v_isSharedCheck_4114_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4106_)) as u8;
                        if v_isSharedCheck_4114_ == 0 {
                            v___x_4109_ = v___x_4106_;
                            v_isShared_4110_ = v_isSharedCheck_4114_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4107_);
                            crate::leanh::lean_dec(v___x_4106_);
                            v___x_4109_ = crate::leanh::lean_box(0);
                            v_isShared_4110_ = v_isSharedCheck_4114_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_4115_ = crate::leanh::lean_ctor_get(v___x_4106_, 0);
                        v_isSharedCheck_4122_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4106_)) as u8;
                        if v_isSharedCheck_4122_ == 0 {
                            v___x_4117_ = v___x_4106_;
                            v_isShared_4118_ = v_isSharedCheck_4122_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4115_);
                            crate::leanh::lean_dec(v___x_4106_);
                            v___x_4117_ = crate::leanh::lean_box(0);
                            v_isShared_4118_ = v_isSharedCheck_4122_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4100_);
                    crate::leanh::lean_dec_ref(v_src_4039_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_4038_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_4037_);
                    crate::leanh::lean_dec_ref(v_dep_4033_);
                    v___x_4123_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_4124_ = lean_string_append(v_name_4036_, v___x_4123_);
                    v___x_4125_ = lean_string_append(v___x_4124_, v_pkgDir_4061_);
                    crate::leanh::lean_dec_ref(v_pkgDir_4061_);
                    v___x_4126_ = 3;
                    v___x_4127_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4127_, 0, v___x_4125_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4127_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4126_,
                    );
                    crate::leanh::lean_inc_ref(v_a_4040_);
                    v___x_4128_ = crate::leanh::lean_apply_2(
                        v_a_4040_,
                        v___x_4127_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_4129_ = crate::leanh::lean_box(0);
                    v___x_4130_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4130_, 0, v___x_4129_);
                    return v___x_4130_;
                }
            }
            10 => {
                if v_isShared_4110_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4109_, 1);
                    v___x_4112_ = v___x_4109_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
                    v___x_4112_ = v_reuseFailAlloc_4113_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_4066_ = v___x_4104_;
                v___y_4067_ = v___x_4105_;
                v___y_4068_ = v_val_4101_;
                v___y_4069_ = v___x_4062_;
                v_val_4070_ = v___x_4112_;
                state = 4;
                continue;
            }
            12 => {
                if v_isShared_4118_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4117_, 0);
                    v___x_4120_ = v___x_4117_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
                    v___x_4120_ = v_reuseFailAlloc_4121_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_4066_ = v___x_4104_;
                v___y_4067_ = v___x_4105_;
                v___y_4068_ = v_val_4101_;
                v___y_4069_ = v___x_4062_;
                v_val_4070_ = v___x_4120_;
                state = 4;
                continue;
            }
            14 => {
                v___x_4135_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once
                    ),
                    _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5,
                );
                if v___x_4135_ == 0 {
                    v_a_4100_ = v_val_4134_;
                    state = 9;
                    continue;
                } else {
                    v___x_4136_ = crate::leanh::lean_box(0);
                    v___x_4137_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_4137_ == 0 {
                        if v___x_4135_ == 0 {
                            v_a_4100_ = v_val_4134_;
                            state = 9;
                            continue;
                        } else {
                            v___x_4138_ = 0usize;
                            v___x_4139_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_2450__overap_4140_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_4062_,
                                    v___f_4064_,
                                    v___x_4132_,
                                    v___x_4138_,
                                    v___x_4139_,
                                    v___x_4136_,
                                );
                            crate::leanh::lean_inc_ref(v_a_4040_);
                            v___x_4141_ = crate::leanh::lean_apply_2(
                                v___x_2450__overap_4140_,
                                v_a_4040_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_4141_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4141_, 1);
                                v_a_4100_ = v_val_4134_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_4134_);
                                crate::leanh::lean_dec_ref(v_pkgDir_4061_);
                                crate::leanh::lean_dec_ref(v_src_4039_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_4038_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_4037_);
                                crate::leanh::lean_dec_ref(v_name_4036_);
                                crate::leanh::lean_dec_ref(v_dep_4033_);
                                v_a_4142_ = crate::leanh::lean_ctor_get(v___x_4141_, 0);
                                v_isSharedCheck_4149_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4141_)) as u8;
                                if v_isSharedCheck_4149_ == 0 {
                                    v___x_4144_ = v___x_4141_;
                                    v_isShared_4145_ = v_isSharedCheck_4149_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4142_);
                                    crate::leanh::lean_dec(v___x_4141_);
                                    v___x_4144_ = crate::leanh::lean_box(0);
                                    v_isShared_4145_ = v_isSharedCheck_4149_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4150_ = 0usize;
                        v___x_4151_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_2460__overap_4152_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_4062_,
                                v___f_4064_,
                                v___x_4132_,
                                v___x_4150_,
                                v___x_4151_,
                                v___x_4136_,
                            );
                        crate::leanh::lean_inc_ref(v_a_4040_);
                        v___x_4153_ = crate::leanh::lean_apply_2(
                            v___x_2460__overap_4152_,
                            v_a_4040_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4153_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4153_, 1);
                            v_a_4100_ = v_val_4134_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_4134_);
                            crate::leanh::lean_dec_ref(v_pkgDir_4061_);
                            crate::leanh::lean_dec_ref(v_src_4039_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_4038_);
                            crate::leanh::lean_dec_ref(v_relPkgDir_4037_);
                            crate::leanh::lean_dec_ref(v_name_4036_);
                            crate::leanh::lean_dec_ref(v_dep_4033_);
                            v_a_4154_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                            v_isSharedCheck_4161_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4153_)) as u8;
                            if v_isSharedCheck_4161_ == 0 {
                                v___x_4156_ = v___x_4153_;
                                v_isShared_4157_ = v_isSharedCheck_4161_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4154_);
                                crate::leanh::lean_dec(v___x_4153_);
                                v___x_4156_ = crate::leanh::lean_box(0);
                                v_isShared_4157_ = v_isSharedCheck_4161_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            15 => {
                if v_isShared_4145_ == 0 {
                    v___x_4147_ = v___x_4144_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
                    v___x_4147_ = v_reuseFailAlloc_4148_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4147_;
            }
            17 => {
                if v_isShared_4157_ == 0 {
                    v___x_4159_ = v___x_4156_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
                    v___x_4159_ = v_reuseFailAlloc_4160_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___boxed(
    mut v_dep_4166_: *mut crate::leanh::LeanObject,
    mut v_inherited_4167_: *mut crate::leanh::LeanObject,
    mut v_wsDir_4168_: *mut crate::leanh::LeanObject,
    mut v_name_4169_: *mut crate::leanh::LeanObject,
    mut v_relPkgDir_4170_: *mut crate::leanh::LeanObject,
    mut v_remoteUrl_4171_: *mut crate::leanh::LeanObject,
    mut v_src_4172_: *mut crate::leanh::LeanObject,
    mut v_a_4173_: *mut crate::leanh::LeanObject,
    mut v_a_4174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inherited_boxed_4175_: u8 = 0;
    let mut v_res_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inherited_boxed_4175_ = (crate::leanh::lean_unbox(v_inherited_4167_) as u8);
    v_res_4176_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep(
        v_dep_4166_,
        v_inherited_boxed_4175_,
        v_wsDir_4168_,
        v_name_4169_,
        v_relPkgDir_4170_,
        v_remoteUrl_4171_,
        v_src_4172_,
        v_a_4173_,
    );
    crate::leanh::lean_dec_ref(v_a_4173_);
    return v_res_4176_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(
    mut v_a_4177_: *mut crate::leanh::LeanObject,
    mut v_name_4178_: *mut crate::leanh::LeanObject,
    mut v_repo_4179_: *mut crate::leanh::LeanObject,
    mut v_url_4180_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4183_: u8 = 0;
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: u8 = 0;
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: u8 = 0;
    let mut v___x_4191_: usize = 0;
    let mut v___x_4192_: usize = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: usize = 0;
    let mut v___x_4195_: usize = 0;
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4183_ = l_System_FilePath_isDir(v_repo_4179_);
                v___x_4187_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4188_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once
                    ),
                    _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5,
                );
                if v___x_4188_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_4189_ = crate::leanh::lean_box(0);
                    v___x_4190_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_4190_ == 0 {
                        if v___x_4188_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_4191_ = 0usize;
                            v___x_4192_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_4187_, v___x_4191_, v___x_4192_, v___x_4189_, v_a_4177_);
                            if crate::leanh::lean_obj_tag(v___x_4193_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4193_, 1);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_rev_x3f_4181_);
                                crate::leanh::lean_dec_ref(v_url_4180_);
                                crate::leanh::lean_dec_ref(v_repo_4179_);
                                crate::leanh::lean_dec_ref(v_name_4178_);
                                return v___x_4193_;
                            }
                        }
                    } else {
                        v___x_4194_ = 0usize;
                        v___x_4195_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_4187_, v___x_4194_, v___x_4195_, v___x_4189_, v_a_4177_);
                        if crate::leanh::lean_obj_tag(v___x_4196_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4196_, 1);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_rev_x3f_4181_);
                            crate::leanh::lean_dec_ref(v_url_4180_);
                            crate::leanh::lean_dec_ref(v_repo_4179_);
                            crate::leanh::lean_dec_ref(v_name_4178_);
                            return v___x_4196_;
                        }
                    }
                }
            }
            1 => {
                if v___x_4183_ == 0 {
                    v___x_4185_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_4177_, v_name_4178_, v_repo_4179_, v_url_4180_, v_rev_x3f_4181_);
                    return v___x_4185_;
                } else {
                    v___x_4186_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_4177_, v_name_4178_, v_repo_4179_, v_url_4180_, v_rev_x3f_4181_);
                    return v___x_4186_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0___boxed(
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_name_4198_: *mut crate::leanh::LeanObject,
    mut v_repo_4199_: *mut crate::leanh::LeanObject,
    mut v_url_4200_: *mut crate::leanh::LeanObject,
    mut v_rev_x3f_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4203_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_4197_, v_name_4198_, v_repo_4199_, v_url_4200_, v_rev_x3f_4201_);
    crate::leanh::lean_dec_ref(v_a_4197_);
    return v_res_4203_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(
    mut v_dep_4204_: *mut crate::leanh::LeanObject,
    mut v_inherited_4205_: u8,
    mut v_lakeEnv_4206_: *mut crate::leanh::LeanObject,
    mut v_wsDir_4207_: *mut crate::leanh::LeanObject,
    mut v_name_4208_: *mut crate::leanh::LeanObject,
    mut v_relPkgDir_4209_: *mut crate::leanh::LeanObject,
    mut v_gitUrl_4210_: *mut crate::leanh::LeanObject,
    mut v_remoteUrl_4211_: *mut crate::leanh::LeanObject,
    mut v_inputRev_x3f_4212_: *mut crate::leanh::LeanObject,
    mut v_subDir_x3f_4213_: *mut crate::leanh::LeanObject,
    mut v_a_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___y_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: u8 = 0;
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    let mut v___x_4248_: usize = 0;
    let mut v___x_4249_: usize = 0;
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4254_: u8 = 0;
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4258_: u8 = 0;
    let mut v___x_4259_: usize = 0;
    let mut v___x_4260_: usize = 0;
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4265_: u8 = 0;
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4269_: u8 = 0;
    let mut v___y_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_a_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: u8 = 0;
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: usize = 0;
    let mut v___x_4317_: usize = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4322_: u8 = 0;
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut v___x_4327_: usize = 0;
    let mut v___x_4328_: usize = 0;
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut v___y_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: u8 = 0;
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gitDir_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: usize = 0;
    let mut v___x_4373_: usize = 0;
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4382_: u8 = 0;
    let mut v___x_4383_: usize = 0;
    let mut v___x_4384_: usize = 0;
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4389_: u8 = 0;
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v_a_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: u8 = 0;
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: usize = 0;
    let mut v___x_4404_: usize = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v___x_4414_: usize = 0;
    let mut v___x_4415_: usize = 0;
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4420_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4424_: u8 = 0;
    let mut v_isSharedCheck_4425_: u8 = 0;
    let mut v_unused_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4430_: u8 = 0;
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4434_: u8 = 0;
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut v_unused_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkgUrlMap_4219_ = crate::leanh::lean_ctor_get(v_lakeEnv_4206_, 5);
                v_name_4220_ = crate::leanh::lean_ctor_get(v_dep_4204_, 0);
                v_scope_4221_ = crate::leanh::lean_ctor_get(v_dep_4204_, 1);
                v_isSharedCheck_4437_ = (!crate::leanh::lean_is_exclusive(v_dep_4204_)) as u8;
                if v_isSharedCheck_4437_ == 0 {
                    v_unused_4438_ = crate::leanh::lean_ctor_get(v_dep_4204_, 4);
                    crate::leanh::lean_dec(v_unused_4438_);
                    v_unused_4439_ = crate::leanh::lean_ctor_get(v_dep_4204_, 3);
                    crate::leanh::lean_dec(v_unused_4439_);
                    v_unused_4440_ = crate::leanh::lean_ctor_get(v_dep_4204_, 2);
                    crate::leanh::lean_dec(v_unused_4440_);
                    v___x_4223_ = v_dep_4204_;
                    v_isShared_4224_ = v_isSharedCheck_4437_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_scope_4221_);
                    crate::leanh::lean_inc(v_name_4220_);
                    crate::leanh::lean_dec(v_dep_4204_);
                    v___x_4223_ = crate::leanh::lean_box(0);
                    v_isShared_4224_ = v_isSharedCheck_4437_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4217_ = crate::leanh::lean_box(0);
                v___x_4218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4218_, 0, v___x_4217_);
                return v___x_4218_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_relPkgDir_4209_);
                crate::leanh::lean_inc_ref(v_wsDir_4207_);
                v_gitDir_4356_ = l_Lake_joinRelative(v_wsDir_4207_, v_relPkgDir_4209_);
                v___x_4435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_4219_, v_name_4220_);
                if crate::leanh::lean_obj_tag(v___x_4435_) == 0 {
                    v___y_4358_ = v_gitUrl_4210_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_gitUrl_4210_);
                    v_val_4436_ = crate::leanh::lean_ctor_get(v___x_4435_, 0);
                    crate::leanh::lean_inc(v_val_4436_);
                    crate::leanh::lean_dec_ref_known(v___x_4435_, 1);
                    v___y_4358_ = v_val_4436_;
                    state = 22;
                    continue;
                }
            }
            3 => {
                v___x_4230_ = l_Lake_defaultConfigFile;
                v___x_4231_ = crate::leanh::lean_box(0);
                v___x_4232_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4232_, 0, v_name_4220_);
                crate::leanh::lean_ctor_set(v___x_4232_, 1, v_scope_4221_);
                crate::leanh::lean_ctor_set(v___x_4232_, 2, v___x_4230_);
                crate::leanh::lean_ctor_set(v___x_4232_, 3, v___x_4231_);
                crate::leanh::lean_ctor_set(v___x_4232_, 4, v___y_4227_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4232_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_inherited_4205_,
                );
                if v_isShared_4224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4223_, 4, v___x_4232_);
                    crate::leanh::lean_ctor_set(v___x_4223_, 3, v_a_4229_);
                    crate::leanh::lean_ctor_set(v___x_4223_, 2, v_remoteUrl_4211_);
                    crate::leanh::lean_ctor_set(v___x_4223_, 1, v___y_4226_);
                    crate::leanh::lean_ctor_set(v___x_4223_, 0, v___y_4228_);
                    v___x_4234_ = v___x_4223_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4236_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___y_4228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___y_4226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4236_, 2, v_remoteUrl_4211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4236_, 3, v_a_4229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4236_, 4, v___x_4232_);
                    v___x_4234_ = v_reuseFailAlloc_4236_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4235_, 0, v___x_4234_);
                return v___x_4235_;
            }
            5 => {
                v___x_4244_ = lean_array_get_size(v___y_4242_);
                v___x_4245_ = lean_nat_dec_lt(v___y_4240_, v___x_4244_);
                if v___x_4245_ == 0 {
                    v___y_4226_ = v___y_4239_;
                    v___y_4227_ = v___y_4238_;
                    v___y_4228_ = v___y_4241_;
                    v_a_4229_ = v_val_4243_;
                    state = 3;
                    continue;
                } else {
                    v___x_4246_ = crate::leanh::lean_box(0);
                    v___x_4247_ = lean_nat_dec_le(v___x_4244_, v___x_4244_);
                    if v___x_4247_ == 0 {
                        if v___x_4245_ == 0 {
                            v___y_4226_ = v___y_4239_;
                            v___y_4227_ = v___y_4238_;
                            v___y_4228_ = v___y_4241_;
                            v_a_4229_ = v_val_4243_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4248_ = 0usize;
                            v___x_4249_ = lean_usize_of_nat(v___x_4244_);
                            v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4242_, v___x_4248_, v___x_4249_, v___x_4246_, v_a_4214_);
                            if crate::leanh::lean_obj_tag(v___x_4250_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4250_, 1);
                                v___y_4226_ = v___y_4239_;
                                v___y_4227_ = v___y_4238_;
                                v___y_4228_ = v___y_4241_;
                                v_a_4229_ = v_val_4243_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_val_4243_);
                                crate::leanh::lean_dec_ref(v___y_4241_);
                                crate::leanh::lean_dec_ref(v___y_4239_);
                                crate::leanh::lean_dec_ref(v___y_4238_);
                                crate::leanh::lean_del_object(v___x_4223_);
                                crate::leanh::lean_dec_ref(v_scope_4221_);
                                crate::leanh::lean_dec(v_name_4220_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                                v_a_4251_ = crate::leanh::lean_ctor_get(v___x_4250_, 0);
                                v_isSharedCheck_4258_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4250_)) as u8;
                                if v_isSharedCheck_4258_ == 0 {
                                    v___x_4253_ = v___x_4250_;
                                    v_isShared_4254_ = v_isSharedCheck_4258_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4251_);
                                    crate::leanh::lean_dec(v___x_4250_);
                                    v___x_4253_ = crate::leanh::lean_box(0);
                                    v_isShared_4254_ = v_isSharedCheck_4258_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4259_ = 0usize;
                        v___x_4260_ = lean_usize_of_nat(v___x_4244_);
                        v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4242_, v___x_4259_, v___x_4260_, v___x_4246_, v_a_4214_);
                        if crate::leanh::lean_obj_tag(v___x_4261_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4261_, 1);
                            v___y_4226_ = v___y_4239_;
                            v___y_4227_ = v___y_4238_;
                            v___y_4228_ = v___y_4241_;
                            v_a_4229_ = v_val_4243_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_val_4243_);
                            crate::leanh::lean_dec_ref(v___y_4241_);
                            crate::leanh::lean_dec_ref(v___y_4239_);
                            crate::leanh::lean_dec_ref(v___y_4238_);
                            crate::leanh::lean_del_object(v___x_4223_);
                            crate::leanh::lean_dec_ref(v_scope_4221_);
                            crate::leanh::lean_dec(v_name_4220_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                            v_a_4262_ = crate::leanh::lean_ctor_get(v___x_4261_, 0);
                            v_isSharedCheck_4269_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4261_)) as u8;
                            if v_isSharedCheck_4269_ == 0 {
                                v___x_4264_ = v___x_4261_;
                                v_isShared_4265_ = v_isSharedCheck_4269_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4262_);
                                crate::leanh::lean_dec(v___x_4261_);
                                v___x_4264_ = crate::leanh::lean_box(0);
                                v_isShared_4265_ = v_isSharedCheck_4269_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_4254_ == 0 {
                    v___x_4256_ = v___x_4253_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4257_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
                    v___x_4256_ = v_reuseFailAlloc_4257_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4256_;
            }
            8 => {
                if v_isShared_4265_ == 0 {
                    v___x_4267_ = v___x_4264_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
                    v___x_4267_ = v_reuseFailAlloc_4268_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4267_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_4274_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_4273_);
                    crate::leanh::lean_dec_ref(v_name_4208_);
                    v_val_4275_ = crate::leanh::lean_ctor_get(v_a_4274_, 0);
                    crate::leanh::lean_inc_n(v_val_4275_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_4274_, 1);
                    v___x_4276_ = l_Lake_defaultManifestFile;
                    v___x_4277_ = l_Lake_joinRelative(v_val_4275_, v___x_4276_);
                    v___x_4278_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4279_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_4280_ = l_Lake_Manifest_load(v___x_4277_);
                    if crate::leanh::lean_obj_tag(v___x_4280_) == 0 {
                        v_a_4281_ = crate::leanh::lean_ctor_get(v___x_4280_, 0);
                        v_isSharedCheck_4288_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4280_)) as u8;
                        if v_isSharedCheck_4288_ == 0 {
                            v___x_4283_ = v___x_4280_;
                            v_isShared_4284_ = v_isSharedCheck_4288_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4281_);
                            crate::leanh::lean_dec(v___x_4280_);
                            v___x_4283_ = crate::leanh::lean_box(0);
                            v_isShared_4284_ = v_isSharedCheck_4288_;
                            state = 11;
                            continue;
                        }
                    } else {
                        v_a_4289_ = crate::leanh::lean_ctor_get(v___x_4280_, 0);
                        v_isSharedCheck_4296_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4280_)) as u8;
                        if v_isSharedCheck_4296_ == 0 {
                            v___x_4291_ = v___x_4280_;
                            v_isShared_4292_ = v_isSharedCheck_4296_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4289_);
                            crate::leanh::lean_dec(v___x_4280_);
                            v___x_4291_ = crate::leanh::lean_box(0);
                            v_isShared_4292_ = v_isSharedCheck_4296_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4274_);
                    crate::leanh::lean_dec_ref(v___y_4272_);
                    crate::leanh::lean_dec_ref(v___y_4271_);
                    crate::leanh::lean_del_object(v___x_4223_);
                    crate::leanh::lean_dec_ref(v_scope_4221_);
                    crate::leanh::lean_dec(v_name_4220_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                    v___x_4297_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_4298_ = lean_string_append(v_name_4208_, v___x_4297_);
                    v___x_4299_ = lean_string_append(v___x_4298_, v___y_4273_);
                    crate::leanh::lean_dec_ref(v___y_4273_);
                    v___x_4300_ = 3;
                    v___x_4301_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4301_, 0, v___x_4299_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4301_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4300_,
                    );
                    crate::leanh::lean_inc_ref(v_a_4214_);
                    v___x_4302_ = crate::leanh::lean_apply_2(
                        v_a_4214_,
                        v___x_4301_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_4303_ = crate::leanh::lean_box(0);
                    v___x_4304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4304_, 0, v___x_4303_);
                    return v___x_4304_;
                }
            }
            11 => {
                if v_isShared_4284_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4283_, 1);
                    v___x_4286_ = v___x_4283_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
                    v___x_4286_ = v_reuseFailAlloc_4287_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_4238_ = v___y_4271_;
                v___y_4239_ = v___y_4272_;
                v___y_4240_ = v___x_4278_;
                v___y_4241_ = v_val_4275_;
                v___y_4242_ = v___x_4279_;
                v_val_4243_ = v___x_4286_;
                state = 5;
                continue;
            }
            13 => {
                if v_isShared_4292_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4291_, 0);
                    v___x_4294_ = v___x_4291_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
                    v___x_4294_ = v_reuseFailAlloc_4295_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_4238_ = v___y_4271_;
                v___y_4239_ = v___y_4272_;
                v___y_4240_ = v___x_4278_;
                v___y_4241_ = v_val_4275_;
                v___y_4242_ = v___x_4279_;
                v_val_4243_ = v___x_4294_;
                state = 5;
                continue;
            }
            15 => {
                v___x_4312_ = lean_array_get_size(v___y_4308_);
                v___x_4313_ = lean_nat_dec_lt(v___y_4309_, v___x_4312_);
                if v___x_4313_ == 0 {
                    v___y_4271_ = v___y_4307_;
                    v___y_4272_ = v___y_4306_;
                    v___y_4273_ = v___y_4310_;
                    v_a_4274_ = v_val_4311_;
                    state = 10;
                    continue;
                } else {
                    v___x_4314_ = crate::leanh::lean_box(0);
                    v___x_4315_ = lean_nat_dec_le(v___x_4312_, v___x_4312_);
                    if v___x_4315_ == 0 {
                        if v___x_4313_ == 0 {
                            v___y_4271_ = v___y_4307_;
                            v___y_4272_ = v___y_4306_;
                            v___y_4273_ = v___y_4310_;
                            v_a_4274_ = v_val_4311_;
                            state = 10;
                            continue;
                        } else {
                            v___x_4316_ = 0usize;
                            v___x_4317_ = lean_usize_of_nat(v___x_4312_);
                            v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4308_, v___x_4316_, v___x_4317_, v___x_4314_, v_a_4214_);
                            if crate::leanh::lean_obj_tag(v___x_4318_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4318_, 1);
                                v___y_4271_ = v___y_4307_;
                                v___y_4272_ = v___y_4306_;
                                v___y_4273_ = v___y_4310_;
                                v_a_4274_ = v_val_4311_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_4311_);
                                crate::leanh::lean_dec_ref(v___y_4310_);
                                crate::leanh::lean_dec_ref(v___y_4307_);
                                crate::leanh::lean_dec_ref(v___y_4306_);
                                crate::leanh::lean_del_object(v___x_4223_);
                                crate::leanh::lean_dec_ref(v_scope_4221_);
                                crate::leanh::lean_dec(v_name_4220_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                                crate::leanh::lean_dec_ref(v_name_4208_);
                                v_a_4319_ = crate::leanh::lean_ctor_get(v___x_4318_, 0);
                                v_isSharedCheck_4326_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4318_)) as u8;
                                if v_isSharedCheck_4326_ == 0 {
                                    v___x_4321_ = v___x_4318_;
                                    v_isShared_4322_ = v_isSharedCheck_4326_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4319_);
                                    crate::leanh::lean_dec(v___x_4318_);
                                    v___x_4321_ = crate::leanh::lean_box(0);
                                    v_isShared_4322_ = v_isSharedCheck_4326_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4327_ = 0usize;
                        v___x_4328_ = lean_usize_of_nat(v___x_4312_);
                        v___x_4329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4308_, v___x_4327_, v___x_4328_, v___x_4314_, v_a_4214_);
                        if crate::leanh::lean_obj_tag(v___x_4329_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4329_, 1);
                            v___y_4271_ = v___y_4307_;
                            v___y_4272_ = v___y_4306_;
                            v___y_4273_ = v___y_4310_;
                            v_a_4274_ = v_val_4311_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_4311_);
                            crate::leanh::lean_dec_ref(v___y_4310_);
                            crate::leanh::lean_dec_ref(v___y_4307_);
                            crate::leanh::lean_dec_ref(v___y_4306_);
                            crate::leanh::lean_del_object(v___x_4223_);
                            crate::leanh::lean_dec_ref(v_scope_4221_);
                            crate::leanh::lean_dec(v_name_4220_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                            crate::leanh::lean_dec_ref(v_name_4208_);
                            v_a_4330_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                            v_isSharedCheck_4337_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4329_)) as u8;
                            if v_isSharedCheck_4337_ == 0 {
                                v___x_4332_ = v___x_4329_;
                                v_isShared_4333_ = v_isSharedCheck_4337_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4330_);
                                crate::leanh::lean_dec(v___x_4329_);
                                v___x_4332_ = crate::leanh::lean_box(0);
                                v_isShared_4333_ = v_isSharedCheck_4337_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                }
            }
            16 => {
                if v_isShared_4322_ == 0 {
                    v___x_4324_ = v___x_4321_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
                    v___x_4324_ = v_reuseFailAlloc_4325_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4324_;
            }
            18 => {
                if v_isShared_4333_ == 0 {
                    v___x_4335_ = v___x_4332_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
                    v___x_4335_ = v_reuseFailAlloc_4336_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4335_;
            }
            20 => {
                crate::leanh::lean_inc_ref(v___y_4341_);
                v_pkgDir_4342_ = l_Lake_joinRelative(v_wsDir_4207_, v___y_4341_);
                crate::leanh::lean_inc_ref(v_pkgDir_4342_);
                v___x_4343_ = l_Lake_resolvePath(v_pkgDir_4342_);
                v___x_4344_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4344_, 0, v___y_4339_);
                crate::leanh::lean_ctor_set(v___x_4344_, 1, v___y_4340_);
                crate::leanh::lean_ctor_set(v___x_4344_, 2, v_inputRev_x3f_4212_);
                crate::leanh::lean_ctor_set(v___x_4344_, 3, v_subDir_x3f_4213_);
                v___x_4345_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4346_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4347_ = lean_string_utf8_byte_size(v___x_4343_);
                v___x_4348_ = lean_nat_dec_eq(v___x_4347_, v___x_4345_);
                if v___x_4348_ == 0 {
                    v___x_4349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4349_, 0, v___x_4343_);
                    v___y_4306_ = v___y_4341_;
                    v___y_4307_ = v___x_4344_;
                    v___y_4308_ = v___x_4346_;
                    v___y_4309_ = v___x_4345_;
                    v___y_4310_ = v_pkgDir_4342_;
                    v_val_4311_ = v___x_4349_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_4343_);
                    v___x_4350_ = crate::leanh::lean_box(0);
                    v___y_4306_ = v___y_4341_;
                    v___y_4307_ = v___x_4344_;
                    v___y_4308_ = v___x_4346_;
                    v___y_4309_ = v___x_4345_;
                    v___y_4310_ = v_pkgDir_4342_;
                    v_val_4311_ = v___x_4350_;
                    state = 15;
                    continue;
                }
            }
            21 => {
                if crate::leanh::lean_obj_tag(v_subDir_x3f_4213_) == 1 {
                    v_val_4354_ = crate::leanh::lean_ctor_get(v_subDir_x3f_4213_, 0);
                    crate::leanh::lean_inc(v_val_4354_);
                    v___x_4355_ = l_Lake_joinRelative(v_relPkgDir_4209_, v_val_4354_);
                    v___y_4339_ = v___y_4352_;
                    v___y_4340_ = v_a_4353_;
                    v___y_4341_ = v___x_4355_;
                    state = 20;
                    continue;
                } else {
                    v___y_4339_ = v___y_4352_;
                    v___y_4340_ = v_a_4353_;
                    v___y_4341_ = v_relPkgDir_4209_;
                    state = 20;
                    continue;
                }
            }
            22 => {
                crate::leanh::lean_inc(v_inputRev_x3f_4212_);
                crate::leanh::lean_inc_ref(v___y_4358_);
                crate::leanh::lean_inc_ref(v_gitDir_4356_);
                crate::leanh::lean_inc_ref(v_name_4208_);
                v___x_4359_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_4214_, v_name_4208_, v_gitDir_4356_, v___y_4358_, v_inputRev_x3f_4212_);
                if crate::leanh::lean_obj_tag(v___x_4359_) == 0 {
                    v_isSharedCheck_4425_ = (!crate::leanh::lean_is_exclusive(v___x_4359_)) as u8;
                    if v_isSharedCheck_4425_ == 0 {
                        v_unused_4426_ = crate::leanh::lean_ctor_get(v___x_4359_, 0);
                        crate::leanh::lean_dec(v_unused_4426_);
                        v___x_4361_ = v___x_4359_;
                        v_isShared_4362_ = v_isSharedCheck_4425_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4359_);
                        v___x_4361_ = crate::leanh::lean_box(0);
                        v_isShared_4362_ = v_isSharedCheck_4425_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4358_);
                    crate::leanh::lean_dec_ref(v_gitDir_4356_);
                    crate::leanh::lean_del_object(v___x_4223_);
                    crate::leanh::lean_dec_ref(v_scope_4221_);
                    crate::leanh::lean_dec(v_name_4220_);
                    crate::leanh::lean_dec(v_subDir_x3f_4213_);
                    crate::leanh::lean_dec(v_inputRev_x3f_4212_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_4209_);
                    crate::leanh::lean_dec_ref(v_name_4208_);
                    crate::leanh::lean_dec_ref(v_wsDir_4207_);
                    v_a_4427_ = crate::leanh::lean_ctor_get(v___x_4359_, 0);
                    v_isSharedCheck_4434_ = (!crate::leanh::lean_is_exclusive(v___x_4359_)) as u8;
                    if v_isSharedCheck_4434_ == 0 {
                        v___x_4429_ = v___x_4359_;
                        v_isShared_4430_ = v_isSharedCheck_4434_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4427_);
                        crate::leanh::lean_dec(v___x_4359_);
                        v___x_4429_ = crate::leanh::lean_box(0);
                        v_isShared_4430_ = v_isSharedCheck_4434_;
                        state = 33;
                        continue;
                    }
                }
            }
            23 => {
                v___x_4363_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4364_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4365_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_4356_, v___x_4364_);
                if crate::leanh::lean_obj_tag(v___x_4365_) == 0 {
                    crate::leanh::lean_del_object(v___x_4361_);
                    v_a_4366_ = crate::leanh::lean_ctor_get(v___x_4365_, 0);
                    crate::leanh::lean_inc(v_a_4366_);
                    v_a_4367_ = crate::leanh::lean_ctor_get(v___x_4365_, 1);
                    crate::leanh::lean_inc(v_a_4367_);
                    crate::leanh::lean_dec_ref_known(v___x_4365_, 2);
                    v___x_4368_ = lean_array_get_size(v_a_4367_);
                    v___x_4369_ = lean_nat_dec_lt(v___x_4363_, v___x_4368_);
                    if v___x_4369_ == 0 {
                        crate::leanh::lean_dec(v_a_4367_);
                        v___y_4352_ = v___y_4358_;
                        v_a_4353_ = v_a_4366_;
                        state = 21;
                        continue;
                    } else {
                        v___x_4370_ = crate::leanh::lean_box(0);
                        v___x_4371_ = lean_nat_dec_le(v___x_4368_, v___x_4368_);
                        if v___x_4371_ == 0 {
                            if v___x_4369_ == 0 {
                                crate::leanh::lean_dec(v_a_4367_);
                                v___y_4352_ = v___y_4358_;
                                v_a_4353_ = v_a_4366_;
                                state = 21;
                                continue;
                            } else {
                                v___x_4372_ = 0usize;
                                v___x_4373_ = lean_usize_of_nat(v___x_4368_);
                                v___x_4374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4367_, v___x_4372_, v___x_4373_, v___x_4370_, v_a_4214_);
                                crate::leanh::lean_dec(v_a_4367_);
                                if crate::leanh::lean_obj_tag(v___x_4374_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4374_, 1);
                                    v___y_4352_ = v___y_4358_;
                                    v_a_4353_ = v_a_4366_;
                                    state = 21;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_4366_);
                                    crate::leanh::lean_dec_ref(v___y_4358_);
                                    crate::leanh::lean_del_object(v___x_4223_);
                                    crate::leanh::lean_dec_ref(v_scope_4221_);
                                    crate::leanh::lean_dec(v_name_4220_);
                                    crate::leanh::lean_dec(v_subDir_x3f_4213_);
                                    crate::leanh::lean_dec(v_inputRev_x3f_4212_);
                                    crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                                    crate::leanh::lean_dec_ref(v_relPkgDir_4209_);
                                    crate::leanh::lean_dec_ref(v_name_4208_);
                                    crate::leanh::lean_dec_ref(v_wsDir_4207_);
                                    v_a_4375_ = crate::leanh::lean_ctor_get(v___x_4374_, 0);
                                    v_isSharedCheck_4382_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4374_)) as u8;
                                    if v_isSharedCheck_4382_ == 0 {
                                        v___x_4377_ = v___x_4374_;
                                        v_isShared_4378_ = v_isSharedCheck_4382_;
                                        state = 24;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4375_);
                                        crate::leanh::lean_dec(v___x_4374_);
                                        v___x_4377_ = crate::leanh::lean_box(0);
                                        v_isShared_4378_ = v_isSharedCheck_4382_;
                                        state = 24;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_4383_ = 0usize;
                            v___x_4384_ = lean_usize_of_nat(v___x_4368_);
                            v___x_4385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4367_, v___x_4383_, v___x_4384_, v___x_4370_, v_a_4214_);
                            crate::leanh::lean_dec(v_a_4367_);
                            if crate::leanh::lean_obj_tag(v___x_4385_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4385_, 1);
                                v___y_4352_ = v___y_4358_;
                                v_a_4353_ = v_a_4366_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_4366_);
                                crate::leanh::lean_dec_ref(v___y_4358_);
                                crate::leanh::lean_del_object(v___x_4223_);
                                crate::leanh::lean_dec_ref(v_scope_4221_);
                                crate::leanh::lean_dec(v_name_4220_);
                                crate::leanh::lean_dec(v_subDir_x3f_4213_);
                                crate::leanh::lean_dec(v_inputRev_x3f_4212_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_4209_);
                                crate::leanh::lean_dec_ref(v_name_4208_);
                                crate::leanh::lean_dec_ref(v_wsDir_4207_);
                                v_a_4386_ = crate::leanh::lean_ctor_get(v___x_4385_, 0);
                                v_isSharedCheck_4393_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4385_)) as u8;
                                if v_isSharedCheck_4393_ == 0 {
                                    v___x_4388_ = v___x_4385_;
                                    v_isShared_4389_ = v_isSharedCheck_4393_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4386_);
                                    crate::leanh::lean_dec(v___x_4385_);
                                    v___x_4388_ = crate::leanh::lean_box(0);
                                    v_isShared_4389_ = v_isSharedCheck_4393_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4358_);
                    crate::leanh::lean_del_object(v___x_4223_);
                    crate::leanh::lean_dec_ref(v_scope_4221_);
                    crate::leanh::lean_dec(v_name_4220_);
                    crate::leanh::lean_dec(v_subDir_x3f_4213_);
                    crate::leanh::lean_dec(v_inputRev_x3f_4212_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_4211_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_4209_);
                    crate::leanh::lean_dec_ref(v_name_4208_);
                    crate::leanh::lean_dec_ref(v_wsDir_4207_);
                    v_a_4394_ = crate::leanh::lean_ctor_get(v___x_4365_, 1);
                    crate::leanh::lean_inc(v_a_4394_);
                    crate::leanh::lean_dec_ref_known(v___x_4365_, 2);
                    v___x_4395_ = lean_array_get_size(v_a_4394_);
                    v___x_4396_ = lean_nat_dec_lt(v___x_4363_, v___x_4395_);
                    if v___x_4396_ == 0 {
                        crate::leanh::lean_dec(v_a_4394_);
                        v___x_4397_ = crate::leanh::lean_box(0);
                        if v_isShared_4362_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4361_, 1);
                            crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4397_);
                            v___x_4399_ = v___x_4361_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_4400_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
                            v___x_4399_ = v_reuseFailAlloc_4400_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4361_);
                        v___x_4401_ = crate::leanh::lean_box(0);
                        v___x_4402_ = lean_nat_dec_le(v___x_4395_, v___x_4395_);
                        if v___x_4402_ == 0 {
                            if v___x_4396_ == 0 {
                                crate::leanh::lean_dec(v_a_4394_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4403_ = 0usize;
                                v___x_4404_ = lean_usize_of_nat(v___x_4395_);
                                v___x_4405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4394_, v___x_4403_, v___x_4404_, v___x_4401_, v_a_4214_);
                                crate::leanh::lean_dec(v_a_4394_);
                                if crate::leanh::lean_obj_tag(v___x_4405_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4405_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_4406_ = crate::leanh::lean_ctor_get(v___x_4405_, 0);
                                    v_isSharedCheck_4413_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4405_)) as u8;
                                    if v_isSharedCheck_4413_ == 0 {
                                        v___x_4408_ = v___x_4405_;
                                        v_isShared_4409_ = v_isSharedCheck_4413_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4406_);
                                        crate::leanh::lean_dec(v___x_4405_);
                                        v___x_4408_ = crate::leanh::lean_box(0);
                                        v_isShared_4409_ = v_isSharedCheck_4413_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_4414_ = 0usize;
                            v___x_4415_ = lean_usize_of_nat(v___x_4395_);
                            v___x_4416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4394_, v___x_4414_, v___x_4415_, v___x_4401_, v_a_4214_);
                            crate::leanh::lean_dec(v_a_4394_);
                            if crate::leanh::lean_obj_tag(v___x_4416_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4416_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_4417_ = crate::leanh::lean_ctor_get(v___x_4416_, 0);
                                v_isSharedCheck_4424_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4416_)) as u8;
                                if v_isSharedCheck_4424_ == 0 {
                                    v___x_4419_ = v___x_4416_;
                                    v_isShared_4420_ = v_isSharedCheck_4424_;
                                    state = 31;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4417_);
                                    crate::leanh::lean_dec(v___x_4416_);
                                    v___x_4419_ = crate::leanh::lean_box(0);
                                    v_isShared_4420_ = v_isSharedCheck_4424_;
                                    state = 31;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            24 => {
                if v_isShared_4378_ == 0 {
                    v___x_4380_ = v___x_4377_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
                    v___x_4380_ = v_reuseFailAlloc_4381_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4380_;
            }
            26 => {
                if v_isShared_4389_ == 0 {
                    v___x_4391_ = v___x_4388_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4392_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
                    v___x_4391_ = v_reuseFailAlloc_4392_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4391_;
            }
            28 => {
                return v___x_4399_;
            }
            29 => {
                if v_isShared_4409_ == 0 {
                    v___x_4411_ = v___x_4408_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
                    v___x_4411_ = v_reuseFailAlloc_4412_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4411_;
            }
            31 => {
                if v_isShared_4420_ == 0 {
                    v___x_4422_ = v___x_4419_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
                    v___x_4422_ = v_reuseFailAlloc_4423_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4422_;
            }
            33 => {
                if v_isShared_4430_ == 0 {
                    v___x_4432_ = v___x_4429_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
                    v___x_4432_ = v_reuseFailAlloc_4433_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___boxed(
    mut v_dep_4441_: *mut crate::leanh::LeanObject,
    mut v_inherited_4442_: *mut crate::leanh::LeanObject,
    mut v_lakeEnv_4443_: *mut crate::leanh::LeanObject,
    mut v_wsDir_4444_: *mut crate::leanh::LeanObject,
    mut v_name_4445_: *mut crate::leanh::LeanObject,
    mut v_relPkgDir_4446_: *mut crate::leanh::LeanObject,
    mut v_gitUrl_4447_: *mut crate::leanh::LeanObject,
    mut v_remoteUrl_4448_: *mut crate::leanh::LeanObject,
    mut v_inputRev_x3f_4449_: *mut crate::leanh::LeanObject,
    mut v_subDir_x3f_4450_: *mut crate::leanh::LeanObject,
    mut v_a_4451_: *mut crate::leanh::LeanObject,
    mut v_a_4452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inherited_boxed_4453_: u8 = 0;
    let mut v_res_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inherited_boxed_4453_ = (crate::leanh::lean_unbox(v_inherited_4442_) as u8);
    v_res_4454_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(
        v_dep_4441_,
        v_inherited_boxed_4453_,
        v_lakeEnv_4443_,
        v_wsDir_4444_,
        v_name_4445_,
        v_relPkgDir_4446_,
        v_gitUrl_4447_,
        v_remoteUrl_4448_,
        v_inputRev_x3f_4449_,
        v_subDir_x3f_4450_,
        v_a_4451_,
    );
    crate::leanh::lean_dec_ref(v_a_4451_);
    crate::leanh::lean_dec_ref(v_lakeEnv_4443_);
    return v_res_4454_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(
    mut v_a_4455_: *mut crate::leanh::LeanObject,
    mut v_dep_4456_: *mut crate::leanh::LeanObject,
    mut v_inherited_4457_: u8,
    mut v_lakeEnv_4458_: *mut crate::leanh::LeanObject,
    mut v_wsDir_4459_: *mut crate::leanh::LeanObject,
    mut v_name_4460_: *mut crate::leanh::LeanObject,
    mut v_relPkgDir_4461_: *mut crate::leanh::LeanObject,
    mut v_gitUrl_4462_: *mut crate::leanh::LeanObject,
    mut v_remoteUrl_4463_: *mut crate::leanh::LeanObject,
    mut v_inputRev_x3f_4464_: *mut crate::leanh::LeanObject,
    mut v_subDir_x3f_4465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4475_: u8 = 0;
    let mut v___y_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v___x_4499_: usize = 0;
    let mut v___x_4500_: usize = 0;
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut v___x_4510_: usize = 0;
    let mut v___x_4511_: usize = 0;
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4516_: u8 = 0;
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4520_: u8 = 0;
    let mut v___y_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4539_: u8 = 0;
    let mut v_a_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: u8 = 0;
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: usize = 0;
    let mut v___x_4568_: usize = 0;
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4573_: u8 = 0;
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4577_: u8 = 0;
    let mut v___x_4578_: usize = 0;
    let mut v___x_4579_: usize = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4584_: u8 = 0;
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4588_: u8 = 0;
    let mut v___y_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gitDir_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4613_: u8 = 0;
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: u8 = 0;
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: u8 = 0;
    let mut v___x_4623_: usize = 0;
    let mut v___x_4624_: usize = 0;
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4629_: u8 = 0;
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4633_: u8 = 0;
    let mut v___x_4634_: usize = 0;
    let mut v___x_4635_: usize = 0;
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4640_: u8 = 0;
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4644_: u8 = 0;
    let mut v_a_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: u8 = 0;
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: usize = 0;
    let mut v___x_4655_: usize = 0;
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4660_: u8 = 0;
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v___x_4665_: usize = 0;
    let mut v___x_4666_: usize = 0;
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4671_: u8 = 0;
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut v_isSharedCheck_4676_: u8 = 0;
    let mut v_unused_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4685_: u8 = 0;
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4688_: u8 = 0;
    let mut v_unused_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkgUrlMap_4470_ = crate::leanh::lean_ctor_get(v_lakeEnv_4458_, 5);
                v_name_4471_ = crate::leanh::lean_ctor_get(v_dep_4456_, 0);
                v_scope_4472_ = crate::leanh::lean_ctor_get(v_dep_4456_, 1);
                v_isSharedCheck_4688_ = (!crate::leanh::lean_is_exclusive(v_dep_4456_)) as u8;
                if v_isSharedCheck_4688_ == 0 {
                    v_unused_4689_ = crate::leanh::lean_ctor_get(v_dep_4456_, 4);
                    crate::leanh::lean_dec(v_unused_4689_);
                    v_unused_4690_ = crate::leanh::lean_ctor_get(v_dep_4456_, 3);
                    crate::leanh::lean_dec(v_unused_4690_);
                    v_unused_4691_ = crate::leanh::lean_ctor_get(v_dep_4456_, 2);
                    crate::leanh::lean_dec(v_unused_4691_);
                    v___x_4474_ = v_dep_4456_;
                    v_isShared_4475_ = v_isSharedCheck_4688_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_scope_4472_);
                    crate::leanh::lean_inc(v_name_4471_);
                    crate::leanh::lean_dec(v_dep_4456_);
                    v___x_4474_ = crate::leanh::lean_box(0);
                    v_isShared_4475_ = v_isSharedCheck_4688_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4468_ = crate::leanh::lean_box(0);
                v___x_4469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4469_, 0, v___x_4468_);
                return v___x_4469_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_relPkgDir_4461_);
                crate::leanh::lean_inc_ref(v_wsDir_4459_);
                v_gitDir_4607_ = l_Lake_joinRelative(v_wsDir_4459_, v_relPkgDir_4461_);
                v___x_4686_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_4470_, v_name_4471_);
                if crate::leanh::lean_obj_tag(v___x_4686_) == 0 {
                    v___y_4609_ = v_gitUrl_4462_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_gitUrl_4462_);
                    v_val_4687_ = crate::leanh::lean_ctor_get(v___x_4686_, 0);
                    crate::leanh::lean_inc(v_val_4687_);
                    crate::leanh::lean_dec_ref_known(v___x_4686_, 1);
                    v___y_4609_ = v_val_4687_;
                    state = 22;
                    continue;
                }
            }
            3 => {
                v___x_4481_ = l_Lake_defaultConfigFile;
                v___x_4482_ = crate::leanh::lean_box(0);
                v___x_4483_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4483_, 0, v_name_4471_);
                crate::leanh::lean_ctor_set(v___x_4483_, 1, v_scope_4472_);
                crate::leanh::lean_ctor_set(v___x_4483_, 2, v___x_4481_);
                crate::leanh::lean_ctor_set(v___x_4483_, 3, v___x_4482_);
                crate::leanh::lean_ctor_set(v___x_4483_, 4, v___y_4477_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4483_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_inherited_4457_,
                );
                if v_isShared_4475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4474_, 4, v___x_4483_);
                    crate::leanh::lean_ctor_set(v___x_4474_, 3, v_a_4480_);
                    crate::leanh::lean_ctor_set(v___x_4474_, 2, v_remoteUrl_4463_);
                    crate::leanh::lean_ctor_set(v___x_4474_, 1, v___y_4479_);
                    crate::leanh::lean_ctor_set(v___x_4474_, 0, v___y_4478_);
                    v___x_4485_ = v___x_4474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4487_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___y_4478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4487_, 1, v___y_4479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4487_, 2, v_remoteUrl_4463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4487_, 3, v_a_4480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4487_, 4, v___x_4483_);
                    v___x_4485_ = v_reuseFailAlloc_4487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4486_, 0, v___x_4485_);
                return v___x_4486_;
            }
            5 => {
                v___x_4495_ = lean_array_get_size(v___y_4491_);
                v___x_4496_ = lean_nat_dec_lt(v___y_4490_, v___x_4495_);
                if v___x_4496_ == 0 {
                    v___y_4477_ = v___y_4489_;
                    v___y_4478_ = v___y_4492_;
                    v___y_4479_ = v___y_4493_;
                    v_a_4480_ = v_val_4494_;
                    state = 3;
                    continue;
                } else {
                    v___x_4497_ = crate::leanh::lean_box(0);
                    v___x_4498_ = lean_nat_dec_le(v___x_4495_, v___x_4495_);
                    if v___x_4498_ == 0 {
                        if v___x_4496_ == 0 {
                            v___y_4477_ = v___y_4489_;
                            v___y_4478_ = v___y_4492_;
                            v___y_4479_ = v___y_4493_;
                            v_a_4480_ = v_val_4494_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4499_ = 0usize;
                            v___x_4500_ = lean_usize_of_nat(v___x_4495_);
                            v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4491_, v___x_4499_, v___x_4500_, v___x_4497_, v_a_4455_);
                            if crate::leanh::lean_obj_tag(v___x_4501_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4501_, 1);
                                v___y_4477_ = v___y_4489_;
                                v___y_4478_ = v___y_4492_;
                                v___y_4479_ = v___y_4493_;
                                v_a_4480_ = v_val_4494_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_val_4494_);
                                crate::leanh::lean_dec_ref(v___y_4493_);
                                crate::leanh::lean_dec_ref(v___y_4492_);
                                crate::leanh::lean_dec_ref(v___y_4489_);
                                crate::leanh::lean_del_object(v___x_4474_);
                                crate::leanh::lean_dec_ref(v_scope_4472_);
                                crate::leanh::lean_dec(v_name_4471_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                                v_a_4502_ = crate::leanh::lean_ctor_get(v___x_4501_, 0);
                                v_isSharedCheck_4509_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4501_)) as u8;
                                if v_isSharedCheck_4509_ == 0 {
                                    v___x_4504_ = v___x_4501_;
                                    v_isShared_4505_ = v_isSharedCheck_4509_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4502_);
                                    crate::leanh::lean_dec(v___x_4501_);
                                    v___x_4504_ = crate::leanh::lean_box(0);
                                    v_isShared_4505_ = v_isSharedCheck_4509_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4510_ = 0usize;
                        v___x_4511_ = lean_usize_of_nat(v___x_4495_);
                        v___x_4512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4491_, v___x_4510_, v___x_4511_, v___x_4497_, v_a_4455_);
                        if crate::leanh::lean_obj_tag(v___x_4512_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4512_, 1);
                            v___y_4477_ = v___y_4489_;
                            v___y_4478_ = v___y_4492_;
                            v___y_4479_ = v___y_4493_;
                            v_a_4480_ = v_val_4494_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_val_4494_);
                            crate::leanh::lean_dec_ref(v___y_4493_);
                            crate::leanh::lean_dec_ref(v___y_4492_);
                            crate::leanh::lean_dec_ref(v___y_4489_);
                            crate::leanh::lean_del_object(v___x_4474_);
                            crate::leanh::lean_dec_ref(v_scope_4472_);
                            crate::leanh::lean_dec(v_name_4471_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                            v_a_4513_ = crate::leanh::lean_ctor_get(v___x_4512_, 0);
                            v_isSharedCheck_4520_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4512_)) as u8;
                            if v_isSharedCheck_4520_ == 0 {
                                v___x_4515_ = v___x_4512_;
                                v_isShared_4516_ = v_isSharedCheck_4520_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4513_);
                                crate::leanh::lean_dec(v___x_4512_);
                                v___x_4515_ = crate::leanh::lean_box(0);
                                v_isShared_4516_ = v_isSharedCheck_4520_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_4505_ == 0 {
                    v___x_4507_ = v___x_4504_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
                    v___x_4507_ = v_reuseFailAlloc_4508_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4507_;
            }
            8 => {
                if v_isShared_4516_ == 0 {
                    v___x_4518_ = v___x_4515_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
                    v___x_4518_ = v_reuseFailAlloc_4519_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4518_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_a_4525_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_4523_);
                    crate::leanh::lean_dec_ref(v_name_4460_);
                    v_val_4526_ = crate::leanh::lean_ctor_get(v_a_4525_, 0);
                    crate::leanh::lean_inc_n(v_val_4526_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_4525_, 1);
                    v___x_4527_ = l_Lake_defaultManifestFile;
                    v___x_4528_ = l_Lake_joinRelative(v_val_4526_, v___x_4527_);
                    v___x_4529_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4530_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_4531_ = l_Lake_Manifest_load(v___x_4528_);
                    if crate::leanh::lean_obj_tag(v___x_4531_) == 0 {
                        v_a_4532_ = crate::leanh::lean_ctor_get(v___x_4531_, 0);
                        v_isSharedCheck_4539_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4531_)) as u8;
                        if v_isSharedCheck_4539_ == 0 {
                            v___x_4534_ = v___x_4531_;
                            v_isShared_4535_ = v_isSharedCheck_4539_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4532_);
                            crate::leanh::lean_dec(v___x_4531_);
                            v___x_4534_ = crate::leanh::lean_box(0);
                            v_isShared_4535_ = v_isSharedCheck_4539_;
                            state = 11;
                            continue;
                        }
                    } else {
                        v_a_4540_ = crate::leanh::lean_ctor_get(v___x_4531_, 0);
                        v_isSharedCheck_4547_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4531_)) as u8;
                        if v_isSharedCheck_4547_ == 0 {
                            v___x_4542_ = v___x_4531_;
                            v_isShared_4543_ = v_isSharedCheck_4547_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4540_);
                            crate::leanh::lean_dec(v___x_4531_);
                            v___x_4542_ = crate::leanh::lean_box(0);
                            v_isShared_4543_ = v_isSharedCheck_4547_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4525_);
                    crate::leanh::lean_dec_ref(v___y_4524_);
                    crate::leanh::lean_dec_ref(v___y_4522_);
                    crate::leanh::lean_del_object(v___x_4474_);
                    crate::leanh::lean_dec_ref(v_scope_4472_);
                    crate::leanh::lean_dec(v_name_4471_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                    v___x_4548_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_4549_ = lean_string_append(v_name_4460_, v___x_4548_);
                    v___x_4550_ = lean_string_append(v___x_4549_, v___y_4523_);
                    crate::leanh::lean_dec_ref(v___y_4523_);
                    v___x_4551_ = 3;
                    v___x_4552_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4552_, 0, v___x_4550_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4552_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4551_,
                    );
                    crate::leanh::lean_inc_ref(v_a_4455_);
                    v___x_4553_ = crate::leanh::lean_apply_2(
                        v_a_4455_,
                        v___x_4552_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_4554_ = crate::leanh::lean_box(0);
                    v___x_4555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4555_, 0, v___x_4554_);
                    return v___x_4555_;
                }
            }
            11 => {
                if v_isShared_4535_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4534_, 1);
                    v___x_4537_ = v___x_4534_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
                    v___x_4537_ = v_reuseFailAlloc_4538_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_4489_ = v___y_4522_;
                v___y_4490_ = v___x_4529_;
                v___y_4491_ = v___x_4530_;
                v___y_4492_ = v_val_4526_;
                v___y_4493_ = v___y_4524_;
                v_val_4494_ = v___x_4537_;
                state = 5;
                continue;
            }
            13 => {
                if v_isShared_4543_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4542_, 0);
                    v___x_4545_ = v___x_4542_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
                    v___x_4545_ = v_reuseFailAlloc_4546_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_4489_ = v___y_4522_;
                v___y_4490_ = v___x_4529_;
                v___y_4491_ = v___x_4530_;
                v___y_4492_ = v_val_4526_;
                v___y_4493_ = v___y_4524_;
                v_val_4494_ = v___x_4545_;
                state = 5;
                continue;
            }
            15 => {
                v___x_4563_ = lean_array_get_size(v___y_4559_);
                v___x_4564_ = lean_nat_dec_lt(v___y_4561_, v___x_4563_);
                if v___x_4564_ == 0 {
                    v___y_4522_ = v___y_4557_;
                    v___y_4523_ = v___y_4558_;
                    v___y_4524_ = v___y_4560_;
                    v_a_4525_ = v_val_4562_;
                    state = 10;
                    continue;
                } else {
                    v___x_4565_ = crate::leanh::lean_box(0);
                    v___x_4566_ = lean_nat_dec_le(v___x_4563_, v___x_4563_);
                    if v___x_4566_ == 0 {
                        if v___x_4564_ == 0 {
                            v___y_4522_ = v___y_4557_;
                            v___y_4523_ = v___y_4558_;
                            v___y_4524_ = v___y_4560_;
                            v_a_4525_ = v_val_4562_;
                            state = 10;
                            continue;
                        } else {
                            v___x_4567_ = 0usize;
                            v___x_4568_ = lean_usize_of_nat(v___x_4563_);
                            v___x_4569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4559_, v___x_4567_, v___x_4568_, v___x_4565_, v_a_4455_);
                            if crate::leanh::lean_obj_tag(v___x_4569_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4569_, 1);
                                v___y_4522_ = v___y_4557_;
                                v___y_4523_ = v___y_4558_;
                                v___y_4524_ = v___y_4560_;
                                v_a_4525_ = v_val_4562_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_4562_);
                                crate::leanh::lean_dec_ref(v___y_4560_);
                                crate::leanh::lean_dec_ref(v___y_4558_);
                                crate::leanh::lean_dec_ref(v___y_4557_);
                                crate::leanh::lean_del_object(v___x_4474_);
                                crate::leanh::lean_dec_ref(v_scope_4472_);
                                crate::leanh::lean_dec(v_name_4471_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                                crate::leanh::lean_dec_ref(v_name_4460_);
                                v_a_4570_ = crate::leanh::lean_ctor_get(v___x_4569_, 0);
                                v_isSharedCheck_4577_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4569_)) as u8;
                                if v_isSharedCheck_4577_ == 0 {
                                    v___x_4572_ = v___x_4569_;
                                    v_isShared_4573_ = v_isSharedCheck_4577_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4570_);
                                    crate::leanh::lean_dec(v___x_4569_);
                                    v___x_4572_ = crate::leanh::lean_box(0);
                                    v_isShared_4573_ = v_isSharedCheck_4577_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4578_ = 0usize;
                        v___x_4579_ = lean_usize_of_nat(v___x_4563_);
                        v___x_4580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4559_, v___x_4578_, v___x_4579_, v___x_4565_, v_a_4455_);
                        if crate::leanh::lean_obj_tag(v___x_4580_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4580_, 1);
                            v___y_4522_ = v___y_4557_;
                            v___y_4523_ = v___y_4558_;
                            v___y_4524_ = v___y_4560_;
                            v_a_4525_ = v_val_4562_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_4562_);
                            crate::leanh::lean_dec_ref(v___y_4560_);
                            crate::leanh::lean_dec_ref(v___y_4558_);
                            crate::leanh::lean_dec_ref(v___y_4557_);
                            crate::leanh::lean_del_object(v___x_4474_);
                            crate::leanh::lean_dec_ref(v_scope_4472_);
                            crate::leanh::lean_dec(v_name_4471_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                            crate::leanh::lean_dec_ref(v_name_4460_);
                            v_a_4581_ = crate::leanh::lean_ctor_get(v___x_4580_, 0);
                            v_isSharedCheck_4588_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4580_)) as u8;
                            if v_isSharedCheck_4588_ == 0 {
                                v___x_4583_ = v___x_4580_;
                                v_isShared_4584_ = v_isSharedCheck_4588_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4581_);
                                crate::leanh::lean_dec(v___x_4580_);
                                v___x_4583_ = crate::leanh::lean_box(0);
                                v_isShared_4584_ = v_isSharedCheck_4588_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                }
            }
            16 => {
                if v_isShared_4573_ == 0 {
                    v___x_4575_ = v___x_4572_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
                    v___x_4575_ = v_reuseFailAlloc_4576_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4575_;
            }
            18 => {
                if v_isShared_4584_ == 0 {
                    v___x_4586_ = v___x_4583_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
                    v___x_4586_ = v_reuseFailAlloc_4587_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4586_;
            }
            20 => {
                crate::leanh::lean_inc_ref(v___y_4592_);
                v_pkgDir_4593_ = l_Lake_joinRelative(v_wsDir_4459_, v___y_4592_);
                crate::leanh::lean_inc_ref(v_pkgDir_4593_);
                v___x_4594_ = l_Lake_resolvePath(v_pkgDir_4593_);
                v___x_4595_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4595_, 0, v___y_4591_);
                crate::leanh::lean_ctor_set(v___x_4595_, 1, v___y_4590_);
                crate::leanh::lean_ctor_set(v___x_4595_, 2, v_inputRev_x3f_4464_);
                crate::leanh::lean_ctor_set(v___x_4595_, 3, v_subDir_x3f_4465_);
                v___x_4596_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4597_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4598_ = lean_string_utf8_byte_size(v___x_4594_);
                v___x_4599_ = lean_nat_dec_eq(v___x_4598_, v___x_4596_);
                if v___x_4599_ == 0 {
                    v___x_4600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4600_, 0, v___x_4594_);
                    v___y_4557_ = v___x_4595_;
                    v___y_4558_ = v_pkgDir_4593_;
                    v___y_4559_ = v___x_4597_;
                    v___y_4560_ = v___y_4592_;
                    v___y_4561_ = v___x_4596_;
                    v_val_4562_ = v___x_4600_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_4594_);
                    v___x_4601_ = crate::leanh::lean_box(0);
                    v___y_4557_ = v___x_4595_;
                    v___y_4558_ = v_pkgDir_4593_;
                    v___y_4559_ = v___x_4597_;
                    v___y_4560_ = v___y_4592_;
                    v___y_4561_ = v___x_4596_;
                    v_val_4562_ = v___x_4601_;
                    state = 15;
                    continue;
                }
            }
            21 => {
                if crate::leanh::lean_obj_tag(v_subDir_x3f_4465_) == 1 {
                    v_val_4605_ = crate::leanh::lean_ctor_get(v_subDir_x3f_4465_, 0);
                    crate::leanh::lean_inc(v_val_4605_);
                    v___x_4606_ = l_Lake_joinRelative(v_relPkgDir_4461_, v_val_4605_);
                    v___y_4590_ = v_a_4604_;
                    v___y_4591_ = v___y_4603_;
                    v___y_4592_ = v___x_4606_;
                    state = 20;
                    continue;
                } else {
                    v___y_4590_ = v_a_4604_;
                    v___y_4591_ = v___y_4603_;
                    v___y_4592_ = v_relPkgDir_4461_;
                    state = 20;
                    continue;
                }
            }
            22 => {
                crate::leanh::lean_inc(v_inputRev_x3f_4464_);
                crate::leanh::lean_inc_ref(v___y_4609_);
                crate::leanh::lean_inc_ref(v_gitDir_4607_);
                crate::leanh::lean_inc_ref(v_name_4460_);
                v___x_4610_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_4455_, v_name_4460_, v_gitDir_4607_, v___y_4609_, v_inputRev_x3f_4464_);
                if crate::leanh::lean_obj_tag(v___x_4610_) == 0 {
                    v_isSharedCheck_4676_ = (!crate::leanh::lean_is_exclusive(v___x_4610_)) as u8;
                    if v_isSharedCheck_4676_ == 0 {
                        v_unused_4677_ = crate::leanh::lean_ctor_get(v___x_4610_, 0);
                        crate::leanh::lean_dec(v_unused_4677_);
                        v___x_4612_ = v___x_4610_;
                        v_isShared_4613_ = v_isSharedCheck_4676_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4610_);
                        v___x_4612_ = crate::leanh::lean_box(0);
                        v_isShared_4613_ = v_isSharedCheck_4676_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4609_);
                    crate::leanh::lean_dec_ref(v_gitDir_4607_);
                    crate::leanh::lean_del_object(v___x_4474_);
                    crate::leanh::lean_dec_ref(v_scope_4472_);
                    crate::leanh::lean_dec(v_name_4471_);
                    crate::leanh::lean_dec(v_subDir_x3f_4465_);
                    crate::leanh::lean_dec(v_inputRev_x3f_4464_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_4461_);
                    crate::leanh::lean_dec_ref(v_name_4460_);
                    crate::leanh::lean_dec_ref(v_wsDir_4459_);
                    v_a_4678_ = crate::leanh::lean_ctor_get(v___x_4610_, 0);
                    v_isSharedCheck_4685_ = (!crate::leanh::lean_is_exclusive(v___x_4610_)) as u8;
                    if v_isSharedCheck_4685_ == 0 {
                        v___x_4680_ = v___x_4610_;
                        v_isShared_4681_ = v_isSharedCheck_4685_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4678_);
                        crate::leanh::lean_dec(v___x_4610_);
                        v___x_4680_ = crate::leanh::lean_box(0);
                        v_isShared_4681_ = v_isSharedCheck_4685_;
                        state = 33;
                        continue;
                    }
                }
            }
            23 => {
                v___x_4614_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4615_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4616_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_4607_, v___x_4615_);
                if crate::leanh::lean_obj_tag(v___x_4616_) == 0 {
                    crate::leanh::lean_del_object(v___x_4612_);
                    v_a_4617_ = crate::leanh::lean_ctor_get(v___x_4616_, 0);
                    crate::leanh::lean_inc(v_a_4617_);
                    v_a_4618_ = crate::leanh::lean_ctor_get(v___x_4616_, 1);
                    crate::leanh::lean_inc(v_a_4618_);
                    crate::leanh::lean_dec_ref_known(v___x_4616_, 2);
                    v___x_4619_ = lean_array_get_size(v_a_4618_);
                    v___x_4620_ = lean_nat_dec_lt(v___x_4614_, v___x_4619_);
                    if v___x_4620_ == 0 {
                        crate::leanh::lean_dec(v_a_4618_);
                        v___y_4603_ = v___y_4609_;
                        v_a_4604_ = v_a_4617_;
                        state = 21;
                        continue;
                    } else {
                        v___x_4621_ = crate::leanh::lean_box(0);
                        v___x_4622_ = lean_nat_dec_le(v___x_4619_, v___x_4619_);
                        if v___x_4622_ == 0 {
                            if v___x_4620_ == 0 {
                                crate::leanh::lean_dec(v_a_4618_);
                                v___y_4603_ = v___y_4609_;
                                v_a_4604_ = v_a_4617_;
                                state = 21;
                                continue;
                            } else {
                                v___x_4623_ = 0usize;
                                v___x_4624_ = lean_usize_of_nat(v___x_4619_);
                                v___x_4625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4618_, v___x_4623_, v___x_4624_, v___x_4621_, v_a_4455_);
                                crate::leanh::lean_dec(v_a_4618_);
                                if crate::leanh::lean_obj_tag(v___x_4625_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4625_, 1);
                                    v___y_4603_ = v___y_4609_;
                                    v_a_4604_ = v_a_4617_;
                                    state = 21;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_4617_);
                                    crate::leanh::lean_dec_ref(v___y_4609_);
                                    crate::leanh::lean_del_object(v___x_4474_);
                                    crate::leanh::lean_dec_ref(v_scope_4472_);
                                    crate::leanh::lean_dec(v_name_4471_);
                                    crate::leanh::lean_dec(v_subDir_x3f_4465_);
                                    crate::leanh::lean_dec(v_inputRev_x3f_4464_);
                                    crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                                    crate::leanh::lean_dec_ref(v_relPkgDir_4461_);
                                    crate::leanh::lean_dec_ref(v_name_4460_);
                                    crate::leanh::lean_dec_ref(v_wsDir_4459_);
                                    v_a_4626_ = crate::leanh::lean_ctor_get(v___x_4625_, 0);
                                    v_isSharedCheck_4633_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4625_)) as u8;
                                    if v_isSharedCheck_4633_ == 0 {
                                        v___x_4628_ = v___x_4625_;
                                        v_isShared_4629_ = v_isSharedCheck_4633_;
                                        state = 24;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4626_);
                                        crate::leanh::lean_dec(v___x_4625_);
                                        v___x_4628_ = crate::leanh::lean_box(0);
                                        v_isShared_4629_ = v_isSharedCheck_4633_;
                                        state = 24;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_4634_ = 0usize;
                            v___x_4635_ = lean_usize_of_nat(v___x_4619_);
                            v___x_4636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4618_, v___x_4634_, v___x_4635_, v___x_4621_, v_a_4455_);
                            crate::leanh::lean_dec(v_a_4618_);
                            if crate::leanh::lean_obj_tag(v___x_4636_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4636_, 1);
                                v___y_4603_ = v___y_4609_;
                                v_a_4604_ = v_a_4617_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_4617_);
                                crate::leanh::lean_dec_ref(v___y_4609_);
                                crate::leanh::lean_del_object(v___x_4474_);
                                crate::leanh::lean_dec_ref(v_scope_4472_);
                                crate::leanh::lean_dec(v_name_4471_);
                                crate::leanh::lean_dec(v_subDir_x3f_4465_);
                                crate::leanh::lean_dec(v_inputRev_x3f_4464_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_4461_);
                                crate::leanh::lean_dec_ref(v_name_4460_);
                                crate::leanh::lean_dec_ref(v_wsDir_4459_);
                                v_a_4637_ = crate::leanh::lean_ctor_get(v___x_4636_, 0);
                                v_isSharedCheck_4644_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4636_)) as u8;
                                if v_isSharedCheck_4644_ == 0 {
                                    v___x_4639_ = v___x_4636_;
                                    v_isShared_4640_ = v_isSharedCheck_4644_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4637_);
                                    crate::leanh::lean_dec(v___x_4636_);
                                    v___x_4639_ = crate::leanh::lean_box(0);
                                    v_isShared_4640_ = v_isSharedCheck_4644_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4609_);
                    crate::leanh::lean_del_object(v___x_4474_);
                    crate::leanh::lean_dec_ref(v_scope_4472_);
                    crate::leanh::lean_dec(v_name_4471_);
                    crate::leanh::lean_dec(v_subDir_x3f_4465_);
                    crate::leanh::lean_dec(v_inputRev_x3f_4464_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_4463_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_4461_);
                    crate::leanh::lean_dec_ref(v_name_4460_);
                    crate::leanh::lean_dec_ref(v_wsDir_4459_);
                    v_a_4645_ = crate::leanh::lean_ctor_get(v___x_4616_, 1);
                    crate::leanh::lean_inc(v_a_4645_);
                    crate::leanh::lean_dec_ref_known(v___x_4616_, 2);
                    v___x_4646_ = lean_array_get_size(v_a_4645_);
                    v___x_4647_ = lean_nat_dec_lt(v___x_4614_, v___x_4646_);
                    if v___x_4647_ == 0 {
                        crate::leanh::lean_dec(v_a_4645_);
                        v___x_4648_ = crate::leanh::lean_box(0);
                        if v_isShared_4613_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4612_, 1);
                            crate::leanh::lean_ctor_set(v___x_4612_, 0, v___x_4648_);
                            v___x_4650_ = v___x_4612_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_4651_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
                            v___x_4650_ = v_reuseFailAlloc_4651_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4612_);
                        v___x_4652_ = crate::leanh::lean_box(0);
                        v___x_4653_ = lean_nat_dec_le(v___x_4646_, v___x_4646_);
                        if v___x_4653_ == 0 {
                            if v___x_4647_ == 0 {
                                crate::leanh::lean_dec(v_a_4645_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4654_ = 0usize;
                                v___x_4655_ = lean_usize_of_nat(v___x_4646_);
                                v___x_4656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4645_, v___x_4654_, v___x_4655_, v___x_4652_, v_a_4455_);
                                crate::leanh::lean_dec(v_a_4645_);
                                if crate::leanh::lean_obj_tag(v___x_4656_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4656_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_4657_ = crate::leanh::lean_ctor_get(v___x_4656_, 0);
                                    v_isSharedCheck_4664_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4656_)) as u8;
                                    if v_isSharedCheck_4664_ == 0 {
                                        v___x_4659_ = v___x_4656_;
                                        v_isShared_4660_ = v_isSharedCheck_4664_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4657_);
                                        crate::leanh::lean_dec(v___x_4656_);
                                        v___x_4659_ = crate::leanh::lean_box(0);
                                        v_isShared_4660_ = v_isSharedCheck_4664_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_4665_ = 0usize;
                            v___x_4666_ = lean_usize_of_nat(v___x_4646_);
                            v___x_4667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4645_, v___x_4665_, v___x_4666_, v___x_4652_, v_a_4455_);
                            crate::leanh::lean_dec(v_a_4645_);
                            if crate::leanh::lean_obj_tag(v___x_4667_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4667_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_4668_ = crate::leanh::lean_ctor_get(v___x_4667_, 0);
                                v_isSharedCheck_4675_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4667_)) as u8;
                                if v_isSharedCheck_4675_ == 0 {
                                    v___x_4670_ = v___x_4667_;
                                    v_isShared_4671_ = v_isSharedCheck_4675_;
                                    state = 31;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4668_);
                                    crate::leanh::lean_dec(v___x_4667_);
                                    v___x_4670_ = crate::leanh::lean_box(0);
                                    v_isShared_4671_ = v_isSharedCheck_4675_;
                                    state = 31;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            24 => {
                if v_isShared_4629_ == 0 {
                    v___x_4631_ = v___x_4628_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
                    v___x_4631_ = v_reuseFailAlloc_4632_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4631_;
            }
            26 => {
                if v_isShared_4640_ == 0 {
                    v___x_4642_ = v___x_4639_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
                    v___x_4642_ = v_reuseFailAlloc_4643_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4642_;
            }
            28 => {
                return v___x_4650_;
            }
            29 => {
                if v_isShared_4660_ == 0 {
                    v___x_4662_ = v___x_4659_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
                    v___x_4662_ = v_reuseFailAlloc_4663_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4662_;
            }
            31 => {
                if v_isShared_4671_ == 0 {
                    v___x_4673_ = v___x_4670_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
                    v___x_4673_ = v_reuseFailAlloc_4674_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4673_;
            }
            33 => {
                if v_isShared_4681_ == 0 {
                    v___x_4683_ = v___x_4680_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
                    v___x_4683_ = v_reuseFailAlloc_4684_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0___boxed(
    mut v_a_4692_: *mut crate::leanh::LeanObject,
    mut v_dep_4693_: *mut crate::leanh::LeanObject,
    mut v_inherited_4694_: *mut crate::leanh::LeanObject,
    mut v_lakeEnv_4695_: *mut crate::leanh::LeanObject,
    mut v_wsDir_4696_: *mut crate::leanh::LeanObject,
    mut v_name_4697_: *mut crate::leanh::LeanObject,
    mut v_relPkgDir_4698_: *mut crate::leanh::LeanObject,
    mut v_gitUrl_4699_: *mut crate::leanh::LeanObject,
    mut v_remoteUrl_4700_: *mut crate::leanh::LeanObject,
    mut v_inputRev_x3f_4701_: *mut crate::leanh::LeanObject,
    mut v_subDir_x3f_4702_: *mut crate::leanh::LeanObject,
    mut v_a_4703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inherited_boxed_4704_: u8 = 0;
    let mut v_res_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inherited_boxed_4704_ = (crate::leanh::lean_unbox(v_inherited_4694_) as u8);
    v_res_4705_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_4692_, v_dep_4693_, v_inherited_boxed_4704_, v_lakeEnv_4695_, v_wsDir_4696_, v_name_4697_, v_relPkgDir_4698_, v_gitUrl_4699_, v_remoteUrl_4700_, v_inputRev_x3f_4701_, v_subDir_x3f_4702_);
    crate::leanh::lean_dec_ref(v_lakeEnv_4695_);
    crate::leanh::lean_dec_ref(v_a_4692_);
    return v_res_4705_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4707_ =
        l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0;
    v___x_4708_ = lean_string_utf8_byte_size(v___x_4707_);
    return v___x_4708_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(
    mut v_s_4709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    v___x_4710_ =
        l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0;
    v___x_4711_ = lean_string_utf8_byte_size(v_s_4709_);
    v___x_4712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once), _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
    v___x_4713_ = lean_nat_dec_le(v___x_4712_, v___x_4711_);
    if v___x_4713_ == 0 {
        let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_4709_);
        v___x_4714_ = crate::leanh::lean_box(0);
        return v___x_4714_;
    } else {
        let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4716_: u8 = 0;
        v___x_4715_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4716_ = lean_string_memcmp(
            v_s_4709_,
            v___x_4710_,
            v___x_4715_,
            v___x_4715_,
            v___x_4712_,
        );
        if v___x_4716_ == 0 {
            let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_s_4709_);
            v___x_4717_ = crate::leanh::lean_box(0);
            return v___x_4717_;
        } else {
            let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_s_4709_);
            v___x_4718_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4718_, 0, v_s_4709_);
            crate::leanh::lean_ctor_set(v___x_4718_, 1, v___x_4715_);
            crate::leanh::lean_ctor_set(v___x_4718_, 2, v___x_4711_);
            v___x_4719_ = l_String_Slice_pos_x21(v___x_4718_, v___x_4712_);
            crate::leanh::lean_dec_ref_known(v___x_4718_, 3);
            v___x_4720_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4720_, 0, v_s_4709_);
            crate::leanh::lean_ctor_set(v___x_4720_, 1, v___x_4719_);
            crate::leanh::lean_ctor_set(v___x_4720_, 2, v___x_4711_);
            v___x_4721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4721_, 0, v___x_4720_);
            return v___x_4721_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(
    mut v_s_4722_: *mut crate::leanh::LeanObject,
    mut v_pat_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4724_ =
        l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_s_4722_);
    return v___x_4724_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(
    mut v_s_4725_: *mut crate::leanh::LeanObject,
    mut v_pat_4726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4727_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(
        v_s_4725_,
        v_pat_4726_,
    );
    crate::leanh::lean_dec_ref(v_pat_4726_);
    return v_res_4727_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(
    mut v_ver_4731_: *mut crate::leanh::LeanObject,
    mut v_as_4732_: *mut crate::leanh::LeanObject,
    mut v_sz_4733_: usize,
    mut v_i_4734_: usize,
    mut v_b_4735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4736_: u8 = 0;
    let mut v_a_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: u8 = 0;
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: usize = 0;
    let mut v___x_4743_: usize = 0;
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4736_ = lean_usize_dec_lt(v_i_4734_, v_sz_4733_);
                if v___x_4736_ == 0 {
                    crate::leanh::lean_inc_ref(v_b_4735_);
                    return v_b_4735_;
                } else {
                    v_a_4737_ = lean_array_uget_borrowed(v_as_4732_, v_i_4734_);
                    v_version_4738_ = crate::leanh::lean_ctor_get(v_a_4737_, 0);
                    v___x_4739_ = crate::leanh::lean_box(0);
                    v___x_4740_ = l_Lake_VerRange_test(v_ver_4731_, v_version_4738_);
                    if v___x_4740_ == 0 {
                        v___x_4741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0;
                        v___x_4742_ = 1usize;
                        v___x_4743_ = lean_usize_add(v_i_4734_, v___x_4742_);
                        v_i_4734_ = v___x_4743_;
                        v_b_4735_ = v___x_4741_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4737_);
                        v___x_4745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4745_, 0, v_a_4737_);
                        v___x_4746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4746_, 0, v___x_4745_);
                        v___x_4747_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4747_, 0, v___x_4746_);
                        crate::leanh::lean_ctor_set(v___x_4747_, 1, v___x_4739_);
                        return v___x_4747_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(
    mut v_ver_4748_: *mut crate::leanh::LeanObject,
    mut v_as_4749_: *mut crate::leanh::LeanObject,
    mut v_sz_4750_: *mut crate::leanh::LeanObject,
    mut v_i_4751_: *mut crate::leanh::LeanObject,
    mut v_b_4752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4753_: usize = 0;
    let mut v_i_boxed_4754_: usize = 0;
    let mut v_res_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4753_ = crate::leanh::lean_unbox_usize(v_sz_4750_);
    crate::leanh::lean_dec(v_sz_4750_);
    v_i_boxed_4754_ = crate::leanh::lean_unbox_usize(v_i_4751_);
    crate::leanh::lean_dec(v_i_4751_);
    v_res_4755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_4748_, v_as_4749_, v_sz_boxed_4753_, v_i_boxed_4754_, v_b_4752_);
    crate::leanh::lean_dec_ref(v_b_4752_);
    crate::leanh::lean_dec_ref(v_as_4749_);
    crate::leanh::lean_dec_ref(v_ver_4748_);
    return v_res_4755_;
}
pub unsafe fn l_Lake_Dependency_materialize(
    mut v_dep_4766_: *mut crate::leanh::LeanObject,
    mut v_inherited_4767_: u8,
    mut v_lakeEnv_4768_: *mut crate::leanh::LeanObject,
    mut v_wsDir_4769_: *mut crate::leanh::LeanObject,
    mut v_relPkgsDir_4770_: *mut crate::leanh::LeanObject,
    mut v_relParentDir_4771_: *mut crate::leanh::LeanObject,
    mut v_a_4772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullName_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rev_x3f_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_src_x3f_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toString_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: u8 = 0;
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4853_: u8 = 0;
    let mut v_unused_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4857_: usize = 0;
    let mut v___x_4858_: usize = 0;
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_revision_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: u8 = 0;
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4883_: u8 = 0;
    let mut v___x_4884_: u8 = 0;
    let mut v_sname_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v_dir_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4892_: u8 = 0;
    let mut v_relPkgDir_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: u8 = 0;
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: u8 = 0;
    let mut v___x_4918_: usize = 0;
    let mut v___x_4919_: usize = 0;
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4924_: u8 = 0;
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut v___x_4929_: usize = 0;
    let mut v___x_4930_: usize = 0;
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_a_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut v_a_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: u8 = 0;
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: u8 = 0;
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: u8 = 0;
    let mut v___x_4979_: usize = 0;
    let mut v___x_4980_: usize = 0;
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4985_: u8 = 0;
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4989_: u8 = 0;
    let mut v___x_4990_: usize = 0;
    let mut v___x_4991_: usize = 0;
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4996_: u8 = 0;
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: u8 = 0;
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_isSharedCheck_5009_: u8 = 0;
    let mut v_unused_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rev_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subDir_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: u8 = 0;
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: u8 = 0;
    let mut v___x_5042_: usize = 0;
    let mut v___x_5043_: usize = 0;
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5048_: u8 = 0;
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5052_: u8 = 0;
    let mut v___x_5053_: usize = 0;
    let mut v___x_5054_: usize = 0;
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5059_: u8 = 0;
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5063_: u8 = 0;
    let mut v___y_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: u8 = 0;
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5081_: u8 = 0;
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v_url_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_githubUrl_x3f_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultBranch_x3f_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subDir_x3f_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullName_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: u8 = 0;
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: usize = 0;
    let mut v___x_5110_: usize = 0;
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5119_: u8 = 0;
    let mut v___x_5120_: usize = 0;
    let mut v___x_5121_: usize = 0;
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5126_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5130_: u8 = 0;
    let mut v_val_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: u8 = 0;
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: usize = 0;
    let mut v___x_5136_: usize = 0;
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5141_: u8 = 0;
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5145_: u8 = 0;
    let mut v___x_5146_: usize = 0;
    let mut v___x_5147_: usize = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5152_: u8 = 0;
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut v_rev_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: u8 = 0;
    let mut v___x_5162_: usize = 0;
    let mut v___x_5163_: usize = 0;
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5168_: u8 = 0;
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut v___x_5173_: usize = 0;
    let mut v___x_5174_: usize = 0;
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut v_ver_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut v_isSharedCheck_5198_: u8 = 0;
    let mut v___y_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: u8 = 0;
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: u8 = 0;
    let mut v___x_5208_: usize = 0;
    let mut v___x_5209_: usize = 0;
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5214_: u8 = 0;
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5218_: u8 = 0;
    let mut v___x_5219_: usize = 0;
    let mut v___x_5220_: usize = 0;
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5229_: u8 = 0;
    let mut v___x_5230_: u8 = 0;
    let mut v_a_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5247_: u8 = 0;
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5252_: u8 = 0;
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5257_: u8 = 0;
    let mut v___x_5258_: u8 = 0;
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5270_: u8 = 0;
    let mut v_a_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5274_: u8 = 0;
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5278_: u8 = 0;
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: u8 = 0;
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_4808_ = crate::leanh::lean_ctor_get(v_dep_4766_, 0);
                v_scope_4809_ = crate::leanh::lean_ctor_get(v_dep_4766_, 1);
                v_version_x3f_4810_ = crate::leanh::lean_ctor_get(v_dep_4766_, 2);
                v_src_x3f_4811_ = crate::leanh::lean_ctor_get(v_dep_4766_, 3);
                crate::leanh::lean_inc(v_src_x3f_4811_);
                if crate::leanh::lean_obj_tag(v_src_x3f_4811_) == 1 {
                    v_val_4880_ = crate::leanh::lean_ctor_get(v_src_x3f_4811_, 0);
                    v_isSharedCheck_5025_ =
                        (!crate::leanh::lean_is_exclusive(v_src_x3f_4811_)) as u8;
                    if v_isSharedCheck_5025_ == 0 {
                        v___x_4882_ = v_src_x3f_4811_;
                        v_isShared_4883_ = v_isSharedCheck_5025_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4880_);
                        crate::leanh::lean_dec(v_src_x3f_4811_);
                        v___x_4882_ = crate::leanh::lean_box(0);
                        v_isShared_4883_ = v_isSharedCheck_5025_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_src_x3f_4811_);
                    crate::leanh::lean_dec_ref(v_relParentDir_4771_);
                    v___x_5026_ = lean_string_utf8_byte_size(v_scope_4809_);
                    v___x_5027_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5230_ = lean_nat_dec_eq(v___x_5026_, v___x_5027_);
                    if v___x_5230_ == 0 {
                        if crate::leanh::lean_obj_tag(v_version_x3f_4810_) == 1 {
                            v_val_5242_ = crate::leanh::lean_ctor_get(v_version_x3f_4810_, 0);
                            crate::leanh::lean_inc(v_val_5242_);
                            v___x_5243_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_val_5242_);
                            if crate::leanh::lean_obj_tag(v___x_5243_) == 1 {
                                v_val_5244_ = crate::leanh::lean_ctor_get(v___x_5243_, 0);
                                v_isSharedCheck_5252_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5243_)) as u8;
                                if v_isSharedCheck_5252_ == 0 {
                                    v___x_5246_ = v___x_5243_;
                                    v_isShared_5247_ = v_isSharedCheck_5252_;
                                    state = 61;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_5244_);
                                    crate::leanh::lean_dec(v___x_5243_);
                                    v___x_5246_ = crate::leanh::lean_box(0);
                                    v_isShared_5247_ = v_isSharedCheck_5252_;
                                    state = 61;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_5243_);
                                crate::leanh::lean_inc(v_val_5242_);
                                v___x_5253_ = l_Lake_VerRange_parse(v_val_5242_);
                                if crate::leanh::lean_obj_tag(v___x_5253_) == 0 {
                                    crate::leanh::lean_inc(v_name_4808_);
                                    crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                                    crate::leanh::lean_dec_ref(v_wsDir_4769_);
                                    crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                                    crate::leanh::lean_dec_ref(v_dep_4766_);
                                    v_a_5254_ = crate::leanh::lean_ctor_get(v___x_5253_, 0);
                                    v_isSharedCheck_5270_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5253_)) as u8;
                                    if v_isSharedCheck_5270_ == 0 {
                                        v___x_5256_ = v___x_5253_;
                                        v_isShared_5257_ = v_isSharedCheck_5270_;
                                        state = 63;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5254_);
                                        crate::leanh::lean_dec(v___x_5253_);
                                        v___x_5256_ = crate::leanh::lean_box(0);
                                        v_isShared_5257_ = v_isSharedCheck_5270_;
                                        state = 63;
                                        continue;
                                    }
                                } else {
                                    v_a_5271_ = crate::leanh::lean_ctor_get(v___x_5253_, 0);
                                    v_isSharedCheck_5278_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5253_)) as u8;
                                    if v_isSharedCheck_5278_ == 0 {
                                        v___x_5273_ = v___x_5253_;
                                        v_isShared_5274_ = v_isSharedCheck_5278_;
                                        state = 65;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5271_);
                                        crate::leanh::lean_dec(v___x_5253_);
                                        v___x_5273_ = crate::leanh::lean_box(0);
                                        v_isShared_5274_ = v_isSharedCheck_5278_;
                                        state = 65;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_5279_ = crate::leanh::lean_box(0);
                            v_a_5232_ = v___x_5279_;
                            state = 60;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_name_4808_);
                        crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                        crate::leanh::lean_dec_ref(v_wsDir_4769_);
                        crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                        crate::leanh::lean_dec_ref(v_dep_4766_);
                        v___x_5280_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_4808_,
                                v___x_5230_,
                            );
                        v___x_5281_ = l_Lake_Dependency_materialize___closed__9;
                        v___x_5282_ = lean_string_append(v___x_5280_, v___x_5281_);
                        v___x_5283_ = 3;
                        v___x_5284_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5284_, 0, v___x_5282_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5284_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5283_,
                        );
                        crate::leanh::lean_inc_ref(v_a_4772_);
                        v___x_5285_ = crate::leanh::lean_apply_2(
                            v_a_4772_,
                            v___x_5284_,
                            crate::leanh::lean_box(0),
                        );
                        v___x_5286_ = crate::leanh::lean_box(0);
                        v___x_5287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5287_, 0, v___x_5286_);
                        return v___x_5287_;
                    }
                }
            }
            1 => {
                v___x_4775_ = crate::leanh::lean_box(0);
                v___x_4776_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4776_, 0, v___x_4775_);
                return v___x_4776_;
            }
            2 => {
                v_fullName_4780_ = crate::leanh::lean_ctor_get(v___y_4778_, 1);
                crate::leanh::lean_inc_ref(v_fullName_4780_);
                crate::leanh::lean_dec_ref(v___y_4778_);
                v___x_4781_ = l_Lake_Dependency_materialize___closed__0;
                v___x_4782_ = lean_string_append(v_fullName_4780_, v___x_4781_);
                v___x_4783_ = 3;
                v___x_4784_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4784_, 0, v___x_4782_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4784_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4783_,
                );
                crate::leanh::lean_inc_ref(v___y_4779_);
                v___x_4785_ =
                    crate::leanh::lean_apply_2(v___y_4779_, v___x_4784_, crate::leanh::lean_box(0));
                v___x_4786_ = crate::leanh::lean_box(0);
                v___x_4787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4787_, 0, v___x_4786_);
                return v___x_4787_;
            }
            3 => {
                v___x_4796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4796_, 0, v___y_4789_);
                v___x_4797_ =
                    l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(
                        v_dep_4766_,
                        v_inherited_4767_,
                        v_lakeEnv_4768_,
                        v_wsDir_4769_,
                        v___y_4793_,
                        v___y_4792_,
                        v___y_4794_,
                        v___y_4795_,
                        v___x_4796_,
                        v___y_4790_,
                        v___y_4791_,
                    );
                crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                return v___x_4797_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_4799_) == 0 {
                    v___x_4806_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                    v___y_4789_ = v_rev_x3f_4804_;
                    v___y_4790_ = v___y_4800_;
                    v___y_4791_ = v___y_4805_;
                    v___y_4792_ = v___y_4801_;
                    v___y_4793_ = v___y_4802_;
                    v___y_4794_ = v___y_4803_;
                    v___y_4795_ = v___x_4806_;
                    state = 3;
                    continue;
                } else {
                    v_val_4807_ = crate::leanh::lean_ctor_get(v___y_4799_, 0);
                    crate::leanh::lean_inc(v_val_4807_);
                    crate::leanh::lean_dec_ref_known(v___y_4799_, 1);
                    v___y_4789_ = v_rev_x3f_4804_;
                    v___y_4790_ = v___y_4800_;
                    v___y_4791_ = v___y_4805_;
                    v___y_4792_ = v___y_4801_;
                    v___y_4793_ = v___y_4802_;
                    v___y_4794_ = v___y_4803_;
                    v___y_4795_ = v_val_4807_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v_toString_4815_ = crate::leanh::lean_ctor_get(v___y_4814_, 0);
                crate::leanh::lean_inc_ref(v_toString_4815_);
                crate::leanh::lean_dec_ref(v___y_4814_);
                v___x_4816_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                v___x_4817_ = lean_string_append(v_scope_4809_, v___x_4816_);
                v___x_4818_ = lean_string_append(v___x_4817_, v___y_4813_);
                crate::leanh::lean_dec_ref(v___y_4813_);
                v___x_4819_ = l_Lake_Dependency_materialize___closed__1;
                v___x_4820_ = lean_string_append(v___x_4818_, v___x_4819_);
                v___x_4821_ = lean_string_append(v___x_4820_, v_toString_4815_);
                crate::leanh::lean_dec_ref(v_toString_4815_);
                v___x_4822_ = l_Lake_Dependency_materialize___closed__2;
                v___x_4823_ = lean_string_append(v___x_4821_, v___x_4822_);
                v___x_4824_ = 3;
                v___x_4825_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4825_, 0, v___x_4823_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4825_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4824_,
                );
                crate::leanh::lean_inc_ref(v_a_4772_);
                v___x_4826_ =
                    crate::leanh::lean_apply_2(v_a_4772_, v___x_4825_, crate::leanh::lean_box(0));
                v___x_4827_ = crate::leanh::lean_box(0);
                v___x_4828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4828_, 0, v___x_4827_);
                return v___x_4828_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_4837_) == 0 {
                    crate::leanh::lean_inc_ref(v_scope_4809_);
                    crate::leanh::lean_dec_ref(v___y_4836_);
                    crate::leanh::lean_dec_ref(v___y_4835_);
                    crate::leanh::lean_dec_ref(v___y_4834_);
                    crate::leanh::lean_dec_ref(v___y_4833_);
                    crate::leanh::lean_dec(v___y_4832_);
                    crate::leanh::lean_dec(v___y_4831_);
                    crate::leanh::lean_dec_ref(v_wsDir_4769_);
                    crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                    crate::leanh::lean_dec_ref(v_dep_4766_);
                    v_isSharedCheck_4853_ = (!crate::leanh::lean_is_exclusive(v_a_4837_)) as u8;
                    if v_isSharedCheck_4853_ == 0 {
                        v_unused_4854_ = crate::leanh::lean_ctor_get(v_a_4837_, 0);
                        crate::leanh::lean_dec(v_unused_4854_);
                        v___x_4839_ = v_a_4837_;
                        v_isShared_4840_ = v_isSharedCheck_4853_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4837_);
                        v___x_4839_ = crate::leanh::lean_box(0);
                        v_isShared_4840_ = v_isSharedCheck_4853_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_4855_ = crate::leanh::lean_ctor_get(v_a_4837_, 0);
                    crate::leanh::lean_inc(v_a_4855_);
                    crate::leanh::lean_dec_ref_known(v_a_4837_, 1);
                    v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0;
                    v_sz_4857_ = lean_array_size(v_a_4855_);
                    v___x_4858_ = 0usize;
                    v___x_4859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_4836_, v_a_4855_, v_sz_4857_, v___x_4858_, v___x_4856_);
                    crate::leanh::lean_dec(v_a_4855_);
                    v_fst_4860_ = crate::leanh::lean_ctor_get(v___x_4859_, 0);
                    crate::leanh::lean_inc(v_fst_4860_);
                    crate::leanh::lean_dec_ref(v___x_4859_);
                    if crate::leanh::lean_obj_tag(v_fst_4860_) == 0 {
                        crate::leanh::lean_inc_ref(v_scope_4809_);
                        crate::leanh::lean_dec_ref(v___y_4835_);
                        crate::leanh::lean_dec_ref(v___y_4834_);
                        crate::leanh::lean_dec_ref(v___y_4833_);
                        crate::leanh::lean_dec(v___y_4832_);
                        crate::leanh::lean_dec(v___y_4831_);
                        crate::leanh::lean_dec_ref(v_wsDir_4769_);
                        crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                        crate::leanh::lean_dec_ref(v_dep_4766_);
                        v___y_4813_ = v___y_4830_;
                        v___y_4814_ = v___y_4836_;
                        state = 5;
                        continue;
                    } else {
                        v_val_4861_ = crate::leanh::lean_ctor_get(v_fst_4860_, 0);
                        crate::leanh::lean_inc(v_val_4861_);
                        crate::leanh::lean_dec_ref_known(v_fst_4860_, 1);
                        if crate::leanh::lean_obj_tag(v_val_4861_) == 1 {
                            crate::leanh::lean_dec_ref(v___y_4836_);
                            v_val_4862_ = crate::leanh::lean_ctor_get(v_val_4861_, 0);
                            crate::leanh::lean_inc(v_val_4862_);
                            crate::leanh::lean_dec_ref_known(v_val_4861_, 1);
                            v_version_4863_ = crate::leanh::lean_ctor_get(v_val_4862_, 0);
                            crate::leanh::lean_inc_ref(v_version_4863_);
                            v_revision_4864_ = crate::leanh::lean_ctor_get(v_val_4862_, 1);
                            crate::leanh::lean_inc_ref(v_revision_4864_);
                            crate::leanh::lean_dec(v_val_4862_);
                            v___x_4865_ =
                                l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                            crate::leanh::lean_inc_ref(v_scope_4809_);
                            v___x_4866_ = lean_string_append(v_scope_4809_, v___x_4865_);
                            v___x_4867_ = lean_string_append(v___x_4866_, v___y_4830_);
                            crate::leanh::lean_dec_ref(v___y_4830_);
                            v___x_4868_ = l_Lake_Dependency_materialize___closed__4;
                            v___x_4869_ = lean_string_append(v___x_4867_, v___x_4868_);
                            v___x_4870_ = l_Lake_StdVer_toString(v_version_4863_);
                            v___x_4871_ = lean_string_append(v___x_4869_, v___x_4870_);
                            crate::leanh::lean_dec_ref(v___x_4870_);
                            v___x_4872_ = l_Lake_Dependency_materialize___closed__5;
                            v___x_4873_ = lean_string_append(v___x_4871_, v___x_4872_);
                            v___x_4874_ = lean_string_append(v___x_4873_, v_revision_4864_);
                            v___x_4875_ = l_Lake_Dependency_materialize___closed__6;
                            v___x_4876_ = lean_string_append(v___x_4874_, v___x_4875_);
                            v___x_4877_ = 1;
                            v___x_4878_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_4878_, 0, v___x_4876_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_4878_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_4877_,
                            );
                            crate::leanh::lean_inc_ref(v_a_4772_);
                            v___x_4879_ = crate::leanh::lean_apply_2(
                                v_a_4772_,
                                v___x_4878_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_4799_ = v___y_4831_;
                            v___y_4800_ = v___y_4832_;
                            v___y_4801_ = v___y_4833_;
                            v___y_4802_ = v___y_4834_;
                            v___y_4803_ = v___y_4835_;
                            v_rev_x3f_4804_ = v_revision_4864_;
                            v___y_4805_ = v_a_4772_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_scope_4809_);
                            crate::leanh::lean_dec(v_val_4861_);
                            crate::leanh::lean_dec_ref(v___y_4835_);
                            crate::leanh::lean_dec_ref(v___y_4834_);
                            crate::leanh::lean_dec_ref(v___y_4833_);
                            crate::leanh::lean_dec(v___y_4832_);
                            crate::leanh::lean_dec(v___y_4831_);
                            crate::leanh::lean_dec_ref(v_wsDir_4769_);
                            crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                            crate::leanh::lean_dec_ref(v_dep_4766_);
                            v___y_4813_ = v___y_4830_;
                            v___y_4814_ = v___y_4836_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_4841_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                v___x_4842_ = lean_string_append(v_scope_4809_, v___x_4841_);
                v___x_4843_ = lean_string_append(v___x_4842_, v___y_4830_);
                crate::leanh::lean_dec_ref(v___y_4830_);
                v___x_4844_ = l_Lake_Dependency_materialize___closed__3;
                v___x_4845_ = lean_string_append(v___x_4843_, v___x_4844_);
                v___x_4846_ = 3;
                v___x_4847_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4847_, 0, v___x_4845_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4847_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4846_,
                );
                crate::leanh::lean_inc_ref(v_a_4772_);
                v___x_4848_ =
                    crate::leanh::lean_apply_2(v_a_4772_, v___x_4847_, crate::leanh::lean_box(0));
                v___x_4849_ = crate::leanh::lean_box(0);
                if v_isShared_4840_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4839_, 1);
                    crate::leanh::lean_ctor_set(v___x_4839_, 0, v___x_4849_);
                    v___x_4851_ = v___x_4839_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4852_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
                    v___x_4851_ = v_reuseFailAlloc_4852_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4851_;
            }
            9 => {
                v___x_4884_ = 0;
                crate::leanh::lean_inc(v_name_4808_);
                v_sname_4885_ = l_Lean_Name_toString(v_name_4808_, v___x_4884_);
                if crate::leanh::lean_obj_tag(v_val_4880_) == 0 {
                    crate::leanh::lean_inc_ref(v_scope_4809_);
                    crate::leanh::lean_inc(v_name_4808_);
                    crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                    crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                    v_isSharedCheck_5009_ = (!crate::leanh::lean_is_exclusive(v_dep_4766_)) as u8;
                    if v_isSharedCheck_5009_ == 0 {
                        v_unused_5010_ = crate::leanh::lean_ctor_get(v_dep_4766_, 4);
                        crate::leanh::lean_dec(v_unused_5010_);
                        v_unused_5011_ = crate::leanh::lean_ctor_get(v_dep_4766_, 3);
                        crate::leanh::lean_dec(v_unused_5011_);
                        v_unused_5012_ = crate::leanh::lean_ctor_get(v_dep_4766_, 2);
                        crate::leanh::lean_dec(v_unused_5012_);
                        v_unused_5013_ = crate::leanh::lean_ctor_get(v_dep_4766_, 1);
                        crate::leanh::lean_dec(v_unused_5013_);
                        v_unused_5014_ = crate::leanh::lean_ctor_get(v_dep_4766_, 0);
                        crate::leanh::lean_dec(v_unused_5014_);
                        v___x_4887_ = v_dep_4766_;
                        v_isShared_4888_ = v_isSharedCheck_5009_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_dep_4766_);
                        v___x_4887_ = crate::leanh::lean_box(0);
                        v_isShared_4888_ = v_isSharedCheck_5009_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4882_);
                    crate::leanh::lean_dec_ref(v_relParentDir_4771_);
                    v_url_5015_ = crate::leanh::lean_ctor_get(v_val_4880_, 0);
                    crate::leanh::lean_inc_ref_n(v_url_5015_, 2);
                    v_rev_5016_ = crate::leanh::lean_ctor_get(v_val_4880_, 1);
                    crate::leanh::lean_inc(v_rev_5016_);
                    v_subDir_5017_ = crate::leanh::lean_ctor_get(v_val_4880_, 2);
                    crate::leanh::lean_inc(v_subDir_5017_);
                    crate::leanh::lean_dec_ref_known(v_val_4880_, 3);
                    v___x_5022_ = l_Lake_Git_filterUrl_x3f(v_url_5015_);
                    if crate::leanh::lean_obj_tag(v___x_5022_) == 0 {
                        v___x_5023_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                        v___y_5019_ = v___x_5023_;
                        state = 31;
                        continue;
                    } else {
                        v_val_5024_ = crate::leanh::lean_ctor_get(v___x_5022_, 0);
                        crate::leanh::lean_inc(v_val_5024_);
                        crate::leanh::lean_dec_ref_known(v___x_5022_, 1);
                        v___y_5019_ = v_val_5024_;
                        state = 31;
                        continue;
                    }
                }
            }
            10 => {
                v_dir_4889_ = crate::leanh::lean_ctor_get(v_val_4880_, 0);
                v_isSharedCheck_5008_ = (!crate::leanh::lean_is_exclusive(v_val_4880_)) as u8;
                if v_isSharedCheck_5008_ == 0 {
                    v___x_4891_ = v_val_4880_;
                    v_isShared_4892_ = v_isSharedCheck_5008_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dir_4889_);
                    crate::leanh::lean_dec(v_val_4880_);
                    v___x_4891_ = crate::leanh::lean_box(0);
                    v_isShared_4892_ = v_isSharedCheck_5008_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_relPkgDir_4893_ = l_Lake_joinRelative(v_relParentDir_4771_, v_dir_4889_);
                crate::leanh::lean_inc_ref(v_relPkgDir_4893_);
                if v_isShared_4892_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4891_, 0, v_relPkgDir_4893_);
                    v___x_4895_ = v___x_4891_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_relPkgDir_4893_);
                    v___x_4895_ = v_reuseFailAlloc_5007_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_ref(v_relPkgDir_4893_);
                v_pkgDir_4896_ = l_Lake_joinRelative(v_wsDir_4769_, v_relPkgDir_4893_);
                crate::leanh::lean_inc_ref(v_pkgDir_4896_);
                v___x_4897_ = l_Lake_resolvePath(v_pkgDir_4896_);
                v___x_4898_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                v___x_4972_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4973_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_5001_ = lean_string_utf8_byte_size(v___x_4897_);
                v___x_5002_ = lean_nat_dec_eq(v___x_5001_, v___x_4972_);
                if v___x_5002_ == 0 {
                    if v_isShared_4883_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4882_, 0, v___x_4897_);
                        v___x_5004_ = v___x_4882_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_5005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_4897_);
                        v___x_5004_ = v_reuseFailAlloc_5005_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4897_);
                    crate::leanh::lean_del_object(v___x_4882_);
                    v___x_5006_ = crate::leanh::lean_box(0);
                    v_val_4975_ = v___x_5006_;
                    state = 25;
                    continue;
                }
            }
            13 => {
                v___x_4902_ = l_Lake_defaultConfigFile;
                v___x_4903_ = crate::leanh::lean_box(0);
                v___x_4904_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4904_, 0, v_name_4808_);
                crate::leanh::lean_ctor_set(v___x_4904_, 1, v_scope_4809_);
                crate::leanh::lean_ctor_set(v___x_4904_, 2, v___x_4902_);
                crate::leanh::lean_ctor_set(v___x_4904_, 3, v___x_4903_);
                crate::leanh::lean_ctor_set(v___x_4904_, 4, v___x_4895_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4904_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v_inherited_4767_,
                );
                if v_isShared_4888_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4887_, 4, v___x_4904_);
                    crate::leanh::lean_ctor_set(v___x_4887_, 3, v_a_4901_);
                    crate::leanh::lean_ctor_set(v___x_4887_, 2, v___x_4898_);
                    crate::leanh::lean_ctor_set(v___x_4887_, 1, v_relPkgDir_4893_);
                    crate::leanh::lean_ctor_set(v___x_4887_, 0, v___y_4900_);
                    v___x_4906_ = v___x_4887_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___y_4900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 1, v_relPkgDir_4893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 2, v___x_4898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 3, v_a_4901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 4, v___x_4904_);
                    v___x_4906_ = v_reuseFailAlloc_4908_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4907_, 0, v___x_4906_);
                return v___x_4907_;
            }
            15 => {
                v___x_4914_ = lean_array_get_size(v___y_4911_);
                v___x_4915_ = lean_nat_dec_lt(v___y_4910_, v___x_4914_);
                if v___x_4915_ == 0 {
                    v___y_4900_ = v___y_4912_;
                    v_a_4901_ = v_val_4913_;
                    state = 13;
                    continue;
                } else {
                    v___x_4916_ = crate::leanh::lean_box(0);
                    v___x_4917_ = lean_nat_dec_le(v___x_4914_, v___x_4914_);
                    if v___x_4917_ == 0 {
                        if v___x_4915_ == 0 {
                            v___y_4900_ = v___y_4912_;
                            v_a_4901_ = v_val_4913_;
                            state = 13;
                            continue;
                        } else {
                            v___x_4918_ = 0usize;
                            v___x_4919_ = lean_usize_of_nat(v___x_4914_);
                            v___x_4920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4911_, v___x_4918_, v___x_4919_, v___x_4916_, v_a_4772_);
                            if crate::leanh::lean_obj_tag(v___x_4920_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4920_, 1);
                                v___y_4900_ = v___y_4912_;
                                v_a_4901_ = v_val_4913_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_val_4913_);
                                crate::leanh::lean_dec_ref(v___y_4912_);
                                crate::leanh::lean_dec_ref(v___x_4895_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_4893_);
                                crate::leanh::lean_del_object(v___x_4887_);
                                crate::leanh::lean_dec_ref(v_scope_4809_);
                                crate::leanh::lean_dec(v_name_4808_);
                                v_a_4921_ = crate::leanh::lean_ctor_get(v___x_4920_, 0);
                                v_isSharedCheck_4928_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4920_)) as u8;
                                if v_isSharedCheck_4928_ == 0 {
                                    v___x_4923_ = v___x_4920_;
                                    v_isShared_4924_ = v_isSharedCheck_4928_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4921_);
                                    crate::leanh::lean_dec(v___x_4920_);
                                    v___x_4923_ = crate::leanh::lean_box(0);
                                    v_isShared_4924_ = v_isSharedCheck_4928_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4929_ = 0usize;
                        v___x_4930_ = lean_usize_of_nat(v___x_4914_);
                        v___x_4931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_4911_, v___x_4929_, v___x_4930_, v___x_4916_, v_a_4772_);
                        if crate::leanh::lean_obj_tag(v___x_4931_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4931_, 1);
                            v___y_4900_ = v___y_4912_;
                            v_a_4901_ = v_val_4913_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_val_4913_);
                            crate::leanh::lean_dec_ref(v___y_4912_);
                            crate::leanh::lean_dec_ref(v___x_4895_);
                            crate::leanh::lean_dec_ref(v_relPkgDir_4893_);
                            crate::leanh::lean_del_object(v___x_4887_);
                            crate::leanh::lean_dec_ref(v_scope_4809_);
                            crate::leanh::lean_dec(v_name_4808_);
                            v_a_4932_ = crate::leanh::lean_ctor_get(v___x_4931_, 0);
                            v_isSharedCheck_4939_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4931_)) as u8;
                            if v_isSharedCheck_4939_ == 0 {
                                v___x_4934_ = v___x_4931_;
                                v_isShared_4935_ = v_isSharedCheck_4939_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4932_);
                                crate::leanh::lean_dec(v___x_4931_);
                                v___x_4934_ = crate::leanh::lean_box(0);
                                v_isShared_4935_ = v_isSharedCheck_4939_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                }
            }
            16 => {
                if v_isShared_4924_ == 0 {
                    v___x_4926_ = v___x_4923_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
                    v___x_4926_ = v_reuseFailAlloc_4927_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4926_;
            }
            18 => {
                if v_isShared_4935_ == 0 {
                    v___x_4937_ = v___x_4934_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4938_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
                    v___x_4937_ = v_reuseFailAlloc_4938_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4937_;
            }
            20 => {
                if crate::leanh::lean_obj_tag(v_a_4941_) == 1 {
                    crate::leanh::lean_dec_ref(v_pkgDir_4896_);
                    crate::leanh::lean_dec_ref(v_sname_4885_);
                    v_val_4942_ = crate::leanh::lean_ctor_get(v_a_4941_, 0);
                    crate::leanh::lean_inc_n(v_val_4942_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_4941_, 1);
                    v___x_4943_ = l_Lake_defaultManifestFile;
                    v___x_4944_ = l_Lake_joinRelative(v_val_4942_, v___x_4943_);
                    v___x_4945_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4946_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_4947_ = l_Lake_Manifest_load(v___x_4944_);
                    if crate::leanh::lean_obj_tag(v___x_4947_) == 0 {
                        v_a_4948_ = crate::leanh::lean_ctor_get(v___x_4947_, 0);
                        v_isSharedCheck_4955_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4947_)) as u8;
                        if v_isSharedCheck_4955_ == 0 {
                            v___x_4950_ = v___x_4947_;
                            v_isShared_4951_ = v_isSharedCheck_4955_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4948_);
                            crate::leanh::lean_dec(v___x_4947_);
                            v___x_4950_ = crate::leanh::lean_box(0);
                            v_isShared_4951_ = v_isSharedCheck_4955_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v_a_4956_ = crate::leanh::lean_ctor_get(v___x_4947_, 0);
                        v_isSharedCheck_4963_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4947_)) as u8;
                        if v_isSharedCheck_4963_ == 0 {
                            v___x_4958_ = v___x_4947_;
                            v_isShared_4959_ = v_isSharedCheck_4963_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4956_);
                            crate::leanh::lean_dec(v___x_4947_);
                            v___x_4958_ = crate::leanh::lean_box(0);
                            v_isShared_4959_ = v_isSharedCheck_4963_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4941_);
                    crate::leanh::lean_dec_ref(v___x_4895_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_4893_);
                    crate::leanh::lean_del_object(v___x_4887_);
                    crate::leanh::lean_dec_ref(v_scope_4809_);
                    crate::leanh::lean_dec(v_name_4808_);
                    v___x_4964_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_4965_ = lean_string_append(v_sname_4885_, v___x_4964_);
                    v___x_4966_ = lean_string_append(v___x_4965_, v_pkgDir_4896_);
                    crate::leanh::lean_dec_ref(v_pkgDir_4896_);
                    v___x_4967_ = 3;
                    v___x_4968_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4968_, 0, v___x_4966_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4968_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4967_,
                    );
                    crate::leanh::lean_inc_ref(v_a_4772_);
                    v___x_4969_ = crate::leanh::lean_apply_2(
                        v_a_4772_,
                        v___x_4968_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_4970_ = crate::leanh::lean_box(0);
                    v___x_4971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4971_, 0, v___x_4970_);
                    return v___x_4971_;
                }
            }
            21 => {
                if v_isShared_4951_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4950_, 1);
                    v___x_4953_ = v___x_4950_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
                    v___x_4953_ = v_reuseFailAlloc_4954_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___y_4910_ = v___x_4945_;
                v___y_4911_ = v___x_4946_;
                v___y_4912_ = v_val_4942_;
                v_val_4913_ = v___x_4953_;
                state = 15;
                continue;
            }
            23 => {
                if v_isShared_4959_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4958_, 0);
                    v___x_4961_ = v___x_4958_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
                    v___x_4961_ = v_reuseFailAlloc_4962_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___y_4910_ = v___x_4945_;
                v___y_4911_ = v___x_4946_;
                v___y_4912_ = v_val_4942_;
                v_val_4913_ = v___x_4961_;
                state = 15;
                continue;
            }
            25 => {
                v___x_4976_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once
                    ),
                    _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5,
                );
                if v___x_4976_ == 0 {
                    v_a_4941_ = v_val_4975_;
                    state = 20;
                    continue;
                } else {
                    v___x_4977_ = crate::leanh::lean_box(0);
                    v___x_4978_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_4978_ == 0 {
                        if v___x_4976_ == 0 {
                            v_a_4941_ = v_val_4975_;
                            state = 20;
                            continue;
                        } else {
                            v___x_4979_ = 0usize;
                            v___x_4980_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_4981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_4973_, v___x_4979_, v___x_4980_, v___x_4977_, v_a_4772_);
                            if crate::leanh::lean_obj_tag(v___x_4981_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4981_, 1);
                                v_a_4941_ = v_val_4975_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_4975_);
                                crate::leanh::lean_dec_ref(v_pkgDir_4896_);
                                crate::leanh::lean_dec_ref(v___x_4895_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_4893_);
                                crate::leanh::lean_del_object(v___x_4887_);
                                crate::leanh::lean_dec_ref(v_sname_4885_);
                                crate::leanh::lean_dec_ref(v_scope_4809_);
                                crate::leanh::lean_dec(v_name_4808_);
                                v_a_4982_ = crate::leanh::lean_ctor_get(v___x_4981_, 0);
                                v_isSharedCheck_4989_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4981_)) as u8;
                                if v_isSharedCheck_4989_ == 0 {
                                    v___x_4984_ = v___x_4981_;
                                    v_isShared_4985_ = v_isSharedCheck_4989_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4982_);
                                    crate::leanh::lean_dec(v___x_4981_);
                                    v___x_4984_ = crate::leanh::lean_box(0);
                                    v_isShared_4985_ = v_isSharedCheck_4989_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4990_ = 0usize;
                        v___x_4991_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_4992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_4973_, v___x_4990_, v___x_4991_, v___x_4977_, v_a_4772_);
                        if crate::leanh::lean_obj_tag(v___x_4992_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4992_, 1);
                            v_a_4941_ = v_val_4975_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_4975_);
                            crate::leanh::lean_dec_ref(v_pkgDir_4896_);
                            crate::leanh::lean_dec_ref(v___x_4895_);
                            crate::leanh::lean_dec_ref(v_relPkgDir_4893_);
                            crate::leanh::lean_del_object(v___x_4887_);
                            crate::leanh::lean_dec_ref(v_sname_4885_);
                            crate::leanh::lean_dec_ref(v_scope_4809_);
                            crate::leanh::lean_dec(v_name_4808_);
                            v_a_4993_ = crate::leanh::lean_ctor_get(v___x_4992_, 0);
                            v_isSharedCheck_5000_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4992_)) as u8;
                            if v_isSharedCheck_5000_ == 0 {
                                v___x_4995_ = v___x_4992_;
                                v_isShared_4996_ = v_isSharedCheck_5000_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4993_);
                                crate::leanh::lean_dec(v___x_4992_);
                                v___x_4995_ = crate::leanh::lean_box(0);
                                v_isShared_4996_ = v_isSharedCheck_5000_;
                                state = 28;
                                continue;
                            }
                        }
                    }
                }
            }
            26 => {
                if v_isShared_4985_ == 0 {
                    v___x_4987_ = v___x_4984_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4988_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
                    v___x_4987_ = v_reuseFailAlloc_4988_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4987_;
            }
            28 => {
                if v_isShared_4996_ == 0 {
                    v___x_4998_ = v___x_4995_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
                    v___x_4998_ = v_reuseFailAlloc_4999_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4998_;
            }
            30 => {
                v_val_4975_ = v___x_5004_;
                state = 25;
                continue;
            }
            31 => {
                crate::leanh::lean_inc_ref(v_sname_4885_);
                v___x_5020_ = l_Lake_joinRelative(v_relPkgsDir_4770_, v_sname_4885_);
                v___x_5021_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_4772_, v_dep_4766_, v_inherited_4767_, v_lakeEnv_4768_, v_wsDir_4769_, v_sname_4885_, v___x_5020_, v_url_5015_, v___y_5019_, v_rev_5016_, v_subDir_5017_);
                crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                return v___x_5021_;
            }
            32 => {
                v___x_5038_ = lean_array_get_size(v_snd_5037_);
                v___x_5039_ = lean_nat_dec_lt(v___x_5027_, v___x_5038_);
                if v___x_5039_ == 0 {
                    crate::leanh::lean_dec_ref(v_snd_5037_);
                    v___y_4830_ = v___y_5029_;
                    v___y_4831_ = v___y_5030_;
                    v___y_4832_ = v___y_5031_;
                    v___y_4833_ = v___y_5032_;
                    v___y_4834_ = v___y_5033_;
                    v___y_4835_ = v___y_5035_;
                    v___y_4836_ = v___y_5034_;
                    v_a_4837_ = v_fst_5036_;
                    state = 6;
                    continue;
                } else {
                    v___x_5040_ = crate::leanh::lean_box(0);
                    v___x_5041_ = lean_nat_dec_le(v___x_5038_, v___x_5038_);
                    if v___x_5041_ == 0 {
                        if v___x_5039_ == 0 {
                            crate::leanh::lean_dec_ref(v_snd_5037_);
                            v___y_4830_ = v___y_5029_;
                            v___y_4831_ = v___y_5030_;
                            v___y_4832_ = v___y_5031_;
                            v___y_4833_ = v___y_5032_;
                            v___y_4834_ = v___y_5033_;
                            v___y_4835_ = v___y_5035_;
                            v___y_4836_ = v___y_5034_;
                            v_a_4837_ = v_fst_5036_;
                            state = 6;
                            continue;
                        } else {
                            v___x_5042_ = 0usize;
                            v___x_5043_ = lean_usize_of_nat(v___x_5038_);
                            v___x_5044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_5037_, v___x_5042_, v___x_5043_, v___x_5040_, v_a_4772_);
                            crate::leanh::lean_dec_ref(v_snd_5037_);
                            if crate::leanh::lean_obj_tag(v___x_5044_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5044_, 1);
                                v___y_4830_ = v___y_5029_;
                                v___y_4831_ = v___y_5030_;
                                v___y_4832_ = v___y_5031_;
                                v___y_4833_ = v___y_5032_;
                                v___y_4834_ = v___y_5033_;
                                v___y_4835_ = v___y_5035_;
                                v___y_4836_ = v___y_5034_;
                                v_a_4837_ = v_fst_5036_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_fst_5036_);
                                crate::leanh::lean_dec_ref(v___y_5035_);
                                crate::leanh::lean_dec_ref(v___y_5034_);
                                crate::leanh::lean_dec_ref(v___y_5033_);
                                crate::leanh::lean_dec_ref(v___y_5032_);
                                crate::leanh::lean_dec(v___y_5031_);
                                crate::leanh::lean_dec(v___y_5030_);
                                crate::leanh::lean_dec_ref(v___y_5029_);
                                crate::leanh::lean_dec_ref(v_wsDir_4769_);
                                crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                                crate::leanh::lean_dec_ref(v_dep_4766_);
                                v_a_5045_ = crate::leanh::lean_ctor_get(v___x_5044_, 0);
                                v_isSharedCheck_5052_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5044_)) as u8;
                                if v_isSharedCheck_5052_ == 0 {
                                    v___x_5047_ = v___x_5044_;
                                    v_isShared_5048_ = v_isSharedCheck_5052_;
                                    state = 33;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5045_);
                                    crate::leanh::lean_dec(v___x_5044_);
                                    v___x_5047_ = crate::leanh::lean_box(0);
                                    v_isShared_5048_ = v_isSharedCheck_5052_;
                                    state = 33;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5053_ = 0usize;
                        v___x_5054_ = lean_usize_of_nat(v___x_5038_);
                        v___x_5055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_5037_, v___x_5053_, v___x_5054_, v___x_5040_, v_a_4772_);
                        crate::leanh::lean_dec_ref(v_snd_5037_);
                        if crate::leanh::lean_obj_tag(v___x_5055_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5055_, 1);
                            v___y_4830_ = v___y_5029_;
                            v___y_4831_ = v___y_5030_;
                            v___y_4832_ = v___y_5031_;
                            v___y_4833_ = v___y_5032_;
                            v___y_4834_ = v___y_5033_;
                            v___y_4835_ = v___y_5035_;
                            v___y_4836_ = v___y_5034_;
                            v_a_4837_ = v_fst_5036_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_fst_5036_);
                            crate::leanh::lean_dec_ref(v___y_5035_);
                            crate::leanh::lean_dec_ref(v___y_5034_);
                            crate::leanh::lean_dec_ref(v___y_5033_);
                            crate::leanh::lean_dec_ref(v___y_5032_);
                            crate::leanh::lean_dec(v___y_5031_);
                            crate::leanh::lean_dec(v___y_5030_);
                            crate::leanh::lean_dec_ref(v___y_5029_);
                            crate::leanh::lean_dec_ref(v_wsDir_4769_);
                            crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                            crate::leanh::lean_dec_ref(v_dep_4766_);
                            v_a_5056_ = crate::leanh::lean_ctor_get(v___x_5055_, 0);
                            v_isSharedCheck_5063_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5055_)) as u8;
                            if v_isSharedCheck_5063_ == 0 {
                                v___x_5058_ = v___x_5055_;
                                v_isShared_5059_ = v_isSharedCheck_5063_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5056_);
                                crate::leanh::lean_dec(v___x_5055_);
                                v___x_5058_ = crate::leanh::lean_box(0);
                                v_isShared_5059_ = v_isSharedCheck_5063_;
                                state = 35;
                                continue;
                            }
                        }
                    }
                }
            }
            33 => {
                if v_isShared_5048_ == 0 {
                    v___x_5050_ = v___x_5047_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
                    v___x_5050_ = v_reuseFailAlloc_5051_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5050_;
            }
            35 => {
                if v_isShared_5059_ == 0 {
                    v___x_5061_ = v___x_5058_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
                    v___x_5061_ = v_reuseFailAlloc_5062_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5061_;
            }
            37 => {
                if crate::leanh::lean_obj_tag(v_a_5067_) == 0 {
                    crate::leanh::lean_inc_ref(v_scope_4809_);
                    crate::leanh::lean_dec_ref_known(v_a_5067_, 1);
                    crate::leanh::lean_dec(v___y_5066_);
                    crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                    crate::leanh::lean_dec_ref(v_wsDir_4769_);
                    crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                    crate::leanh::lean_dec_ref(v_dep_4766_);
                    v___x_5068_ =
                        l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                    v___x_5069_ = lean_string_append(v_scope_4809_, v___x_5068_);
                    v___x_5070_ = lean_string_append(v___x_5069_, v___y_5065_);
                    crate::leanh::lean_dec_ref(v___y_5065_);
                    v___x_5071_ = l_Lake_Dependency_materialize___closed__7;
                    v___x_5072_ = lean_string_append(v___x_5070_, v___x_5071_);
                    v___x_5073_ = 3;
                    v___x_5074_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5074_, 0, v___x_5072_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5074_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5073_,
                    );
                    crate::leanh::lean_inc_ref(v_a_4772_);
                    v___x_5075_ = crate::leanh::lean_apply_2(
                        v_a_4772_,
                        v___x_5074_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_5076_ = crate::leanh::lean_box(0);
                    v___x_5077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5077_, 0, v___x_5076_);
                    return v___x_5077_;
                } else {
                    v_a_5078_ = crate::leanh::lean_ctor_get(v_a_5067_, 0);
                    v_isSharedCheck_5198_ = (!crate::leanh::lean_is_exclusive(v_a_5067_)) as u8;
                    if v_isSharedCheck_5198_ == 0 {
                        v___x_5080_ = v_a_5067_;
                        v_isShared_5081_ = v_isSharedCheck_5198_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5078_);
                        crate::leanh::lean_dec(v_a_5067_);
                        v___x_5080_ = crate::leanh::lean_box(0);
                        v_isShared_5081_ = v_isSharedCheck_5198_;
                        state = 38;
                        continue;
                    }
                }
            }
            38 => {
                if crate::leanh::lean_obj_tag(v_a_5078_) == 0 {
                    crate::leanh::lean_inc_ref(v_scope_4809_);
                    crate::leanh::lean_del_object(v___x_5080_);
                    crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                    crate::leanh::lean_dec_ref(v_wsDir_4769_);
                    crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                    crate::leanh::lean_dec_ref(v_dep_4766_);
                    v___x_5082_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(
                        v_scope_4809_,
                        v___y_5065_,
                        v___y_5066_,
                    );
                    crate::leanh::lean_dec_ref(v___y_5065_);
                    v___x_5083_ = 3;
                    v___x_5084_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5084_, 0, v___x_5082_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5084_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5083_,
                    );
                    crate::leanh::lean_inc_ref(v_a_4772_);
                    v___x_5085_ = crate::leanh::lean_apply_2(
                        v_a_4772_,
                        v___x_5084_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_5086_ = crate::leanh::lean_box(0);
                    v___x_5087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5087_, 0, v___x_5086_);
                    return v___x_5087_;
                } else {
                    v_val_5088_ = crate::leanh::lean_ctor_get(v_a_5078_, 0);
                    crate::leanh::lean_inc(v_val_5088_);
                    crate::leanh::lean_dec_ref_known(v_a_5078_, 1);
                    v___x_5089_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_5088_);
                    if crate::leanh::lean_obj_tag(v___x_5089_) == 1 {
                        v_val_5090_ = crate::leanh::lean_ctor_get(v___x_5089_, 0);
                        v_isSharedCheck_5197_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5089_)) as u8;
                        if v_isSharedCheck_5197_ == 0 {
                            v___x_5092_ = v___x_5089_;
                            v_isShared_5093_ = v_isSharedCheck_5197_;
                            state = 39;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5090_);
                            crate::leanh::lean_dec(v___x_5089_);
                            v___x_5092_ = crate::leanh::lean_box(0);
                            v_isShared_5093_ = v_isSharedCheck_5197_;
                            state = 39;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5089_);
                        crate::leanh::lean_del_object(v___x_5080_);
                        crate::leanh::lean_dec(v___y_5066_);
                        crate::leanh::lean_dec_ref(v___y_5065_);
                        crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                        crate::leanh::lean_dec_ref(v_wsDir_4769_);
                        crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                        crate::leanh::lean_dec_ref(v_dep_4766_);
                        v___y_4778_ = v_val_5088_;
                        v___y_4779_ = v_a_4772_;
                        state = 2;
                        continue;
                    }
                }
            }
            39 => {
                if crate::leanh::lean_obj_tag(v_val_5090_) == 0 {
                    v_url_5094_ = crate::leanh::lean_ctor_get(v_val_5090_, 1);
                    crate::leanh::lean_inc_ref(v_url_5094_);
                    v_githubUrl_x3f_5095_ = crate::leanh::lean_ctor_get(v_val_5090_, 2);
                    crate::leanh::lean_inc(v_githubUrl_x3f_5095_);
                    v_defaultBranch_x3f_5096_ = crate::leanh::lean_ctor_get(v_val_5090_, 3);
                    crate::leanh::lean_inc(v_defaultBranch_x3f_5096_);
                    v_subDir_x3f_5097_ = crate::leanh::lean_ctor_get(v_val_5090_, 4);
                    crate::leanh::lean_inc(v_subDir_x3f_5097_);
                    crate::leanh::lean_dec_ref_known(v_val_5090_, 5);
                    v_name_5098_ = crate::leanh::lean_ctor_get(v_val_5088_, 0);
                    crate::leanh::lean_inc_ref(v_name_5098_);
                    v_fullName_5099_ = crate::leanh::lean_ctor_get(v_val_5088_, 1);
                    crate::leanh::lean_inc_ref(v_fullName_5099_);
                    crate::leanh::lean_dec(v_val_5088_);
                    v___x_5100_ = l_Lake_joinRelative(v_relPkgsDir_4770_, v_name_5098_);
                    match crate::leanh::lean_obj_tag(v___y_5066_) {
                        0 => {
                            crate::leanh::lean_del_object(v___x_5080_);
                            crate::leanh::lean_dec_ref(v___y_5065_);
                            v___x_5101_ =
                                l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                            if crate::leanh::lean_obj_tag(v_defaultBranch_x3f_5096_) == 0 {
                                crate::leanh::lean_dec_ref(v___x_5100_);
                                crate::leanh::lean_dec_ref(v_fullName_5099_);
                                crate::leanh::lean_dec(v_subDir_x3f_5097_);
                                crate::leanh::lean_dec(v_githubUrl_x3f_5095_);
                                crate::leanh::lean_dec_ref(v_url_5094_);
                                crate::leanh::lean_dec_ref(v_wsDir_4769_);
                                crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                                crate::leanh::lean_dec_ref(v_dep_4766_);
                                v___x_5102_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
                                if v___x_5102_ == 0 {
                                    v___x_5103_ = crate::leanh::lean_box(0);
                                    if v_isShared_5093_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_5092_, 0, v___x_5103_);
                                        v___x_5105_ = v___x_5092_;
                                        state = 40;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5106_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5106_,
                                            0,
                                            v___x_5103_,
                                        );
                                        v___x_5105_ = v_reuseFailAlloc_5106_;
                                        state = 40;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_5092_);
                                    v___x_5107_ = crate::leanh::lean_box(0);
                                    v___x_5108_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                                    if v___x_5108_ == 0 {
                                        if v___x_5102_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_5109_ = 0usize;
                                            v___x_5110_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                            v___x_5111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5101_, v___x_5109_, v___x_5110_, v___x_5107_, v_a_4772_);
                                            if crate::leanh::lean_obj_tag(v___x_5111_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_5111_, 1);
                                                state = 1;
                                                continue;
                                            } else {
                                                v_a_5112_ =
                                                    crate::leanh::lean_ctor_get(v___x_5111_, 0);
                                                v_isSharedCheck_5119_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5111_))
                                                        as u8;
                                                if v_isSharedCheck_5119_ == 0 {
                                                    v___x_5114_ = v___x_5111_;
                                                    v_isShared_5115_ = v_isSharedCheck_5119_;
                                                    state = 41;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5112_);
                                                    crate::leanh::lean_dec(v___x_5111_);
                                                    v___x_5114_ = crate::leanh::lean_box(0);
                                                    v_isShared_5115_ = v_isSharedCheck_5119_;
                                                    state = 41;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_5120_ = 0usize;
                                        v___x_5121_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                        v___x_5122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5101_, v___x_5120_, v___x_5121_, v___x_5107_, v_a_4772_);
                                        if crate::leanh::lean_obj_tag(v___x_5122_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_5122_, 1);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_5123_ = crate::leanh::lean_ctor_get(v___x_5122_, 0);
                                            v_isSharedCheck_5130_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5122_))
                                                    as u8;
                                            if v_isSharedCheck_5130_ == 0 {
                                                v___x_5125_ = v___x_5122_;
                                                v_isShared_5126_ = v_isSharedCheck_5130_;
                                                state = 43;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5123_);
                                                crate::leanh::lean_dec(v___x_5122_);
                                                v___x_5125_ = crate::leanh::lean_box(0);
                                                v_isShared_5126_ = v_isSharedCheck_5130_;
                                                state = 43;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_5092_);
                                v_val_5131_ =
                                    crate::leanh::lean_ctor_get(v_defaultBranch_x3f_5096_, 0);
                                crate::leanh::lean_inc(v_val_5131_);
                                crate::leanh::lean_dec_ref_known(v_defaultBranch_x3f_5096_, 1);
                                v___x_5132_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
                                if v___x_5132_ == 0 {
                                    v___y_4799_ = v_githubUrl_x3f_5095_;
                                    v___y_4800_ = v_subDir_x3f_5097_;
                                    v___y_4801_ = v___x_5100_;
                                    v___y_4802_ = v_fullName_5099_;
                                    v___y_4803_ = v_url_5094_;
                                    v_rev_x3f_4804_ = v_val_5131_;
                                    v___y_4805_ = v_a_4772_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_5133_ = crate::leanh::lean_box(0);
                                    v___x_5134_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                                    if v___x_5134_ == 0 {
                                        if v___x_5132_ == 0 {
                                            v___y_4799_ = v_githubUrl_x3f_5095_;
                                            v___y_4800_ = v_subDir_x3f_5097_;
                                            v___y_4801_ = v___x_5100_;
                                            v___y_4802_ = v_fullName_5099_;
                                            v___y_4803_ = v_url_5094_;
                                            v_rev_x3f_4804_ = v_val_5131_;
                                            v___y_4805_ = v_a_4772_;
                                            state = 4;
                                            continue;
                                        } else {
                                            v___x_5135_ = 0usize;
                                            v___x_5136_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                            v___x_5137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5101_, v___x_5135_, v___x_5136_, v___x_5133_, v_a_4772_);
                                            if crate::leanh::lean_obj_tag(v___x_5137_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_5137_, 1);
                                                v___y_4799_ = v_githubUrl_x3f_5095_;
                                                v___y_4800_ = v_subDir_x3f_5097_;
                                                v___y_4801_ = v___x_5100_;
                                                v___y_4802_ = v_fullName_5099_;
                                                v___y_4803_ = v_url_5094_;
                                                v_rev_x3f_4804_ = v_val_5131_;
                                                v___y_4805_ = v_a_4772_;
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_val_5131_);
                                                crate::leanh::lean_dec_ref(v___x_5100_);
                                                crate::leanh::lean_dec_ref(v_fullName_5099_);
                                                crate::leanh::lean_dec(v_subDir_x3f_5097_);
                                                crate::leanh::lean_dec(v_githubUrl_x3f_5095_);
                                                crate::leanh::lean_dec_ref(v_url_5094_);
                                                crate::leanh::lean_dec_ref(v_wsDir_4769_);
                                                crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                                                crate::leanh::lean_dec_ref(v_dep_4766_);
                                                v_a_5138_ =
                                                    crate::leanh::lean_ctor_get(v___x_5137_, 0);
                                                v_isSharedCheck_5145_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5137_))
                                                        as u8;
                                                if v_isSharedCheck_5145_ == 0 {
                                                    v___x_5140_ = v___x_5137_;
                                                    v_isShared_5141_ = v_isSharedCheck_5145_;
                                                    state = 45;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5138_);
                                                    crate::leanh::lean_dec(v___x_5137_);
                                                    v___x_5140_ = crate::leanh::lean_box(0);
                                                    v_isShared_5141_ = v_isSharedCheck_5145_;
                                                    state = 45;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_5146_ = 0usize;
                                        v___x_5147_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                        v___x_5148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5101_, v___x_5146_, v___x_5147_, v___x_5133_, v_a_4772_);
                                        if crate::leanh::lean_obj_tag(v___x_5148_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_5148_, 1);
                                            v___y_4799_ = v_githubUrl_x3f_5095_;
                                            v___y_4800_ = v_subDir_x3f_5097_;
                                            v___y_4801_ = v___x_5100_;
                                            v___y_4802_ = v_fullName_5099_;
                                            v___y_4803_ = v_url_5094_;
                                            v_rev_x3f_4804_ = v_val_5131_;
                                            v___y_4805_ = v_a_4772_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_val_5131_);
                                            crate::leanh::lean_dec_ref(v___x_5100_);
                                            crate::leanh::lean_dec_ref(v_fullName_5099_);
                                            crate::leanh::lean_dec(v_subDir_x3f_5097_);
                                            crate::leanh::lean_dec(v_githubUrl_x3f_5095_);
                                            crate::leanh::lean_dec_ref(v_url_5094_);
                                            crate::leanh::lean_dec_ref(v_wsDir_4769_);
                                            crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                                            crate::leanh::lean_dec_ref(v_dep_4766_);
                                            v_a_5149_ = crate::leanh::lean_ctor_get(v___x_5148_, 0);
                                            v_isSharedCheck_5156_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5148_))
                                                    as u8;
                                            if v_isSharedCheck_5156_ == 0 {
                                                v___x_5151_ = v___x_5148_;
                                                v_isShared_5152_ = v_isSharedCheck_5156_;
                                                state = 47;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5149_);
                                                crate::leanh::lean_dec(v___x_5148_);
                                                v___x_5151_ = crate::leanh::lean_box(0);
                                                v_isShared_5152_ = v_isSharedCheck_5156_;
                                                state = 47;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        1 => {
                            crate::leanh::lean_dec(v_defaultBranch_x3f_5096_);
                            crate::leanh::lean_del_object(v___x_5092_);
                            crate::leanh::lean_del_object(v___x_5080_);
                            crate::leanh::lean_dec_ref(v___y_5065_);
                            v_rev_5157_ = crate::leanh::lean_ctor_get(v___y_5066_, 0);
                            crate::leanh::lean_inc_ref(v_rev_5157_);
                            crate::leanh::lean_dec_ref_known(v___y_5066_, 1);
                            v___x_5158_ =
                                l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                            v___x_5159_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
                            if v___x_5159_ == 0 {
                                v___y_4799_ = v_githubUrl_x3f_5095_;
                                v___y_4800_ = v_subDir_x3f_5097_;
                                v___y_4801_ = v___x_5100_;
                                v___y_4802_ = v_fullName_5099_;
                                v___y_4803_ = v_url_5094_;
                                v_rev_x3f_4804_ = v_rev_5157_;
                                v___y_4805_ = v_a_4772_;
                                state = 4;
                                continue;
                            } else {
                                v___x_5160_ = crate::leanh::lean_box(0);
                                v___x_5161_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                                if v___x_5161_ == 0 {
                                    if v___x_5159_ == 0 {
                                        v___y_4799_ = v_githubUrl_x3f_5095_;
                                        v___y_4800_ = v_subDir_x3f_5097_;
                                        v___y_4801_ = v___x_5100_;
                                        v___y_4802_ = v_fullName_5099_;
                                        v___y_4803_ = v_url_5094_;
                                        v_rev_x3f_4804_ = v_rev_5157_;
                                        v___y_4805_ = v_a_4772_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v___x_5162_ = 0usize;
                                        v___x_5163_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                        v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5158_, v___x_5162_, v___x_5163_, v___x_5160_, v_a_4772_);
                                        if crate::leanh::lean_obj_tag(v___x_5164_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_5164_, 1);
                                            v___y_4799_ = v_githubUrl_x3f_5095_;
                                            v___y_4800_ = v_subDir_x3f_5097_;
                                            v___y_4801_ = v___x_5100_;
                                            v___y_4802_ = v_fullName_5099_;
                                            v___y_4803_ = v_url_5094_;
                                            v_rev_x3f_4804_ = v_rev_5157_;
                                            v___y_4805_ = v_a_4772_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_rev_5157_);
                                            crate::leanh::lean_dec_ref(v___x_5100_);
                                            crate::leanh::lean_dec_ref(v_fullName_5099_);
                                            crate::leanh::lean_dec(v_subDir_x3f_5097_);
                                            crate::leanh::lean_dec(v_githubUrl_x3f_5095_);
                                            crate::leanh::lean_dec_ref(v_url_5094_);
                                            crate::leanh::lean_dec_ref(v_wsDir_4769_);
                                            crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                                            crate::leanh::lean_dec_ref(v_dep_4766_);
                                            v_a_5165_ = crate::leanh::lean_ctor_get(v___x_5164_, 0);
                                            v_isSharedCheck_5172_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5164_))
                                                    as u8;
                                            if v_isSharedCheck_5172_ == 0 {
                                                v___x_5167_ = v___x_5164_;
                                                v_isShared_5168_ = v_isSharedCheck_5172_;
                                                state = 49;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5165_);
                                                crate::leanh::lean_dec(v___x_5164_);
                                                v___x_5167_ = crate::leanh::lean_box(0);
                                                v_isShared_5168_ = v_isSharedCheck_5172_;
                                                state = 49;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    v___x_5173_ = 0usize;
                                    v___x_5174_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                    v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5158_, v___x_5173_, v___x_5174_, v___x_5160_, v_a_4772_);
                                    if crate::leanh::lean_obj_tag(v___x_5175_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_5175_, 1);
                                        v___y_4799_ = v_githubUrl_x3f_5095_;
                                        v___y_4800_ = v_subDir_x3f_5097_;
                                        v___y_4801_ = v___x_5100_;
                                        v___y_4802_ = v_fullName_5099_;
                                        v___y_4803_ = v_url_5094_;
                                        v_rev_x3f_4804_ = v_rev_5157_;
                                        v___y_4805_ = v_a_4772_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_rev_5157_);
                                        crate::leanh::lean_dec_ref(v___x_5100_);
                                        crate::leanh::lean_dec_ref(v_fullName_5099_);
                                        crate::leanh::lean_dec(v_subDir_x3f_5097_);
                                        crate::leanh::lean_dec(v_githubUrl_x3f_5095_);
                                        crate::leanh::lean_dec_ref(v_url_5094_);
                                        crate::leanh::lean_dec_ref(v_wsDir_4769_);
                                        crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                                        crate::leanh::lean_dec_ref(v_dep_4766_);
                                        v_a_5176_ = crate::leanh::lean_ctor_get(v___x_5175_, 0);
                                        v_isSharedCheck_5183_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5175_)) as u8;
                                        if v_isSharedCheck_5183_ == 0 {
                                            v___x_5178_ = v___x_5175_;
                                            v_isShared_5179_ = v_isSharedCheck_5183_;
                                            state = 51;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5176_);
                                            crate::leanh::lean_dec(v___x_5175_);
                                            v___x_5178_ = crate::leanh::lean_box(0);
                                            v_isShared_5179_ = v_isSharedCheck_5183_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_defaultBranch_x3f_5096_);
                            crate::leanh::lean_del_object(v___x_5092_);
                            v_ver_5184_ = crate::leanh::lean_ctor_get(v___y_5066_, 0);
                            crate::leanh::lean_inc_ref(v_ver_5184_);
                            crate::leanh::lean_dec_ref_known(v___y_5066_, 1);
                            v___x_5185_ =
                                l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                            crate::leanh::lean_inc_ref(v___y_5065_);
                            crate::leanh::lean_inc_ref(v_scope_4809_);
                            crate::leanh::lean_inc_ref(v_lakeEnv_4768_);
                            v___x_5186_ = l_Lake_Reservoir_fetchPkgVersions(
                                v_lakeEnv_4768_,
                                v_scope_4809_,
                                v___y_5065_,
                                v___x_5185_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5186_) == 0 {
                                v_a_5187_ = crate::leanh::lean_ctor_get(v___x_5186_, 0);
                                crate::leanh::lean_inc(v_a_5187_);
                                v_a_5188_ = crate::leanh::lean_ctor_get(v___x_5186_, 1);
                                crate::leanh::lean_inc(v_a_5188_);
                                crate::leanh::lean_dec_ref_known(v___x_5186_, 2);
                                if v_isShared_5081_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_5080_, 0, v_a_5187_);
                                    v___x_5190_ = v___x_5080_;
                                    state = 53;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5191_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5191_,
                                        0,
                                        v_a_5187_,
                                    );
                                    v___x_5190_ = v_reuseFailAlloc_5191_;
                                    state = 53;
                                    continue;
                                }
                            } else {
                                v_a_5192_ = crate::leanh::lean_ctor_get(v___x_5186_, 0);
                                crate::leanh::lean_inc(v_a_5192_);
                                v_a_5193_ = crate::leanh::lean_ctor_get(v___x_5186_, 1);
                                crate::leanh::lean_inc(v_a_5193_);
                                crate::leanh::lean_dec_ref_known(v___x_5186_, 2);
                                if v_isShared_5081_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_5080_, 0);
                                    crate::leanh::lean_ctor_set(v___x_5080_, 0, v_a_5192_);
                                    v___x_5195_ = v___x_5080_;
                                    state = 54;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5196_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5196_,
                                        0,
                                        v_a_5192_,
                                    );
                                    v___x_5195_ = v_reuseFailAlloc_5196_;
                                    state = 54;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5092_);
                    crate::leanh::lean_dec(v_val_5090_);
                    crate::leanh::lean_del_object(v___x_5080_);
                    crate::leanh::lean_dec(v___y_5066_);
                    crate::leanh::lean_dec_ref(v___y_5065_);
                    crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                    crate::leanh::lean_dec_ref(v_wsDir_4769_);
                    crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                    crate::leanh::lean_dec_ref(v_dep_4766_);
                    v___y_4778_ = v_val_5088_;
                    v___y_4779_ = v_a_4772_;
                    state = 2;
                    continue;
                }
            }
            40 => {
                return v___x_5105_;
            }
            41 => {
                if v_isShared_5115_ == 0 {
                    v___x_5117_ = v___x_5114_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
                    v___x_5117_ = v_reuseFailAlloc_5118_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_5117_;
            }
            43 => {
                if v_isShared_5126_ == 0 {
                    v___x_5128_ = v___x_5125_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
                    v___x_5128_ = v_reuseFailAlloc_5129_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_5128_;
            }
            45 => {
                if v_isShared_5141_ == 0 {
                    v___x_5143_ = v___x_5140_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_5144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
                    v___x_5143_ = v_reuseFailAlloc_5144_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5143_;
            }
            47 => {
                if v_isShared_5152_ == 0 {
                    v___x_5154_ = v___x_5151_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_5155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
                    v___x_5154_ = v_reuseFailAlloc_5155_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_5154_;
            }
            49 => {
                if v_isShared_5168_ == 0 {
                    v___x_5170_ = v___x_5167_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
                    v___x_5170_ = v_reuseFailAlloc_5171_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5170_;
            }
            51 => {
                if v_isShared_5179_ == 0 {
                    v___x_5181_ = v___x_5178_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
                    v___x_5181_ = v_reuseFailAlloc_5182_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5181_;
            }
            53 => {
                v___y_5029_ = v___y_5065_;
                v___y_5030_ = v_githubUrl_x3f_5095_;
                v___y_5031_ = v_subDir_x3f_5097_;
                v___y_5032_ = v___x_5100_;
                v___y_5033_ = v_fullName_5099_;
                v___y_5034_ = v_ver_5184_;
                v___y_5035_ = v_url_5094_;
                v_fst_5036_ = v___x_5190_;
                v_snd_5037_ = v_a_5188_;
                state = 32;
                continue;
            }
            54 => {
                v___y_5029_ = v___y_5065_;
                v___y_5030_ = v_githubUrl_x3f_5095_;
                v___y_5031_ = v_subDir_x3f_5097_;
                v___y_5032_ = v___x_5100_;
                v___y_5033_ = v_fullName_5099_;
                v___y_5034_ = v_ver_5184_;
                v___y_5035_ = v_url_5094_;
                v_fst_5036_ = v___x_5195_;
                v_snd_5037_ = v_a_5193_;
                state = 32;
                continue;
            }
            55 => {
                v___x_5204_ = lean_array_get_size(v_snd_5203_);
                v___x_5205_ = lean_nat_dec_lt(v___x_5027_, v___x_5204_);
                if v___x_5205_ == 0 {
                    crate::leanh::lean_dec_ref(v_snd_5203_);
                    v___y_5065_ = v___y_5200_;
                    v___y_5066_ = v___y_5201_;
                    v_a_5067_ = v_fst_5202_;
                    state = 37;
                    continue;
                } else {
                    v___x_5206_ = crate::leanh::lean_box(0);
                    v___x_5207_ = lean_nat_dec_le(v___x_5204_, v___x_5204_);
                    if v___x_5207_ == 0 {
                        if v___x_5205_ == 0 {
                            crate::leanh::lean_dec_ref(v_snd_5203_);
                            v___y_5065_ = v___y_5200_;
                            v___y_5066_ = v___y_5201_;
                            v_a_5067_ = v_fst_5202_;
                            state = 37;
                            continue;
                        } else {
                            v___x_5208_ = 0usize;
                            v___x_5209_ = lean_usize_of_nat(v___x_5204_);
                            v___x_5210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_5203_, v___x_5208_, v___x_5209_, v___x_5206_, v_a_4772_);
                            crate::leanh::lean_dec_ref(v_snd_5203_);
                            if crate::leanh::lean_obj_tag(v___x_5210_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5210_, 1);
                                v___y_5065_ = v___y_5200_;
                                v___y_5066_ = v___y_5201_;
                                v_a_5067_ = v_fst_5202_;
                                state = 37;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_fst_5202_);
                                crate::leanh::lean_dec(v___y_5201_);
                                crate::leanh::lean_dec_ref(v___y_5200_);
                                crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                                crate::leanh::lean_dec_ref(v_wsDir_4769_);
                                crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                                crate::leanh::lean_dec_ref(v_dep_4766_);
                                v_a_5211_ = crate::leanh::lean_ctor_get(v___x_5210_, 0);
                                v_isSharedCheck_5218_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5210_)) as u8;
                                if v_isSharedCheck_5218_ == 0 {
                                    v___x_5213_ = v___x_5210_;
                                    v_isShared_5214_ = v_isSharedCheck_5218_;
                                    state = 56;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5211_);
                                    crate::leanh::lean_dec(v___x_5210_);
                                    v___x_5213_ = crate::leanh::lean_box(0);
                                    v_isShared_5214_ = v_isSharedCheck_5218_;
                                    state = 56;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5219_ = 0usize;
                        v___x_5220_ = lean_usize_of_nat(v___x_5204_);
                        v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_5203_, v___x_5219_, v___x_5220_, v___x_5206_, v_a_4772_);
                        crate::leanh::lean_dec_ref(v_snd_5203_);
                        if crate::leanh::lean_obj_tag(v___x_5221_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5221_, 1);
                            v___y_5065_ = v___y_5200_;
                            v___y_5066_ = v___y_5201_;
                            v_a_5067_ = v_fst_5202_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_fst_5202_);
                            crate::leanh::lean_dec(v___y_5201_);
                            crate::leanh::lean_dec_ref(v___y_5200_);
                            crate::leanh::lean_dec_ref(v_relPkgsDir_4770_);
                            crate::leanh::lean_dec_ref(v_wsDir_4769_);
                            crate::leanh::lean_dec_ref(v_lakeEnv_4768_);
                            crate::leanh::lean_dec_ref(v_dep_4766_);
                            v_a_5222_ = crate::leanh::lean_ctor_get(v___x_5221_, 0);
                            v_isSharedCheck_5229_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5221_)) as u8;
                            if v_isSharedCheck_5229_ == 0 {
                                v___x_5224_ = v___x_5221_;
                                v_isShared_5225_ = v_isSharedCheck_5229_;
                                state = 58;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5222_);
                                crate::leanh::lean_dec(v___x_5221_);
                                v___x_5224_ = crate::leanh::lean_box(0);
                                v_isShared_5225_ = v_isSharedCheck_5229_;
                                state = 58;
                                continue;
                            }
                        }
                    }
                }
            }
            56 => {
                if v_isShared_5214_ == 0 {
                    v___x_5216_ = v___x_5213_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_5217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
                    v___x_5216_ = v_reuseFailAlloc_5217_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_5216_;
            }
            58 => {
                if v_isShared_5225_ == 0 {
                    v___x_5227_ = v___x_5224_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_5228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
                    v___x_5227_ = v_reuseFailAlloc_5228_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_5227_;
            }
            60 => {
                crate::leanh::lean_inc(v_name_4808_);
                v___x_5233_ = l_Lean_Name_toString(v_name_4808_, v___x_5230_);
                v___x_5234_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                crate::leanh::lean_inc_ref(v___x_5233_);
                crate::leanh::lean_inc_ref(v_scope_4809_);
                crate::leanh::lean_inc_ref(v_lakeEnv_4768_);
                v___x_5235_ = l_Lake_Reservoir_fetchPkg_x3f(
                    v_lakeEnv_4768_,
                    v_scope_4809_,
                    v___x_5233_,
                    v___x_5234_,
                );
                if crate::leanh::lean_obj_tag(v___x_5235_) == 0 {
                    v_a_5236_ = crate::leanh::lean_ctor_get(v___x_5235_, 0);
                    crate::leanh::lean_inc(v_a_5236_);
                    v_a_5237_ = crate::leanh::lean_ctor_get(v___x_5235_, 1);
                    crate::leanh::lean_inc(v_a_5237_);
                    crate::leanh::lean_dec_ref_known(v___x_5235_, 2);
                    v___x_5238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5238_, 0, v_a_5236_);
                    v___y_5200_ = v___x_5233_;
                    v___y_5201_ = v_a_5232_;
                    v_fst_5202_ = v___x_5238_;
                    v_snd_5203_ = v_a_5237_;
                    state = 55;
                    continue;
                } else {
                    v_a_5239_ = crate::leanh::lean_ctor_get(v___x_5235_, 0);
                    crate::leanh::lean_inc(v_a_5239_);
                    v_a_5240_ = crate::leanh::lean_ctor_get(v___x_5235_, 1);
                    crate::leanh::lean_inc(v_a_5240_);
                    crate::leanh::lean_dec_ref_known(v___x_5235_, 2);
                    v___x_5241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5241_, 0, v_a_5239_);
                    v___y_5200_ = v___x_5233_;
                    v___y_5201_ = v_a_5232_;
                    v_fst_5202_ = v___x_5241_;
                    v_snd_5203_ = v_a_5240_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                v___x_5248_ = l_String_Slice_toString(v_val_5244_);
                crate::leanh::lean_dec(v_val_5244_);
                if v_isShared_5247_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5246_, 0, v___x_5248_);
                    v___x_5250_ = v___x_5246_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_5251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5248_);
                    v___x_5250_ = v_reuseFailAlloc_5251_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                v_a_5232_ = v___x_5250_;
                state = 60;
                continue;
            }
            63 => {
                v___x_5258_ = 1;
                v___x_5259_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_4808_,
                    v___x_5258_,
                );
                v___x_5260_ = l_Lake_Dependency_materialize___closed__8;
                v___x_5261_ = lean_string_append(v___x_5259_, v___x_5260_);
                v___x_5262_ = lean_string_append(v___x_5261_, v_a_5254_);
                crate::leanh::lean_dec(v_a_5254_);
                v___x_5263_ = 3;
                v___x_5264_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5264_, 0, v___x_5262_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5264_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5263_,
                );
                crate::leanh::lean_inc_ref(v_a_4772_);
                v___x_5265_ =
                    crate::leanh::lean_apply_2(v_a_4772_, v___x_5264_, crate::leanh::lean_box(0));
                v___x_5266_ = crate::leanh::lean_box(0);
                if v_isShared_5257_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5256_, 1);
                    crate::leanh::lean_ctor_set(v___x_5256_, 0, v___x_5266_);
                    v___x_5268_ = v___x_5256_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_5269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5266_);
                    v___x_5268_ = v_reuseFailAlloc_5269_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_5268_;
            }
            65 => {
                if v_isShared_5274_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5273_, 2);
                    v___x_5276_ = v___x_5273_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_5277_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5271_);
                    v___x_5276_ = v_reuseFailAlloc_5277_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                v_a_5232_ = v___x_5276_;
                state = 60;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Dependency_materialize___boxed(
    mut v_dep_5288_: *mut crate::leanh::LeanObject,
    mut v_inherited_5289_: *mut crate::leanh::LeanObject,
    mut v_lakeEnv_5290_: *mut crate::leanh::LeanObject,
    mut v_wsDir_5291_: *mut crate::leanh::LeanObject,
    mut v_relPkgsDir_5292_: *mut crate::leanh::LeanObject,
    mut v_relParentDir_5293_: *mut crate::leanh::LeanObject,
    mut v_a_5294_: *mut crate::leanh::LeanObject,
    mut v_a_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inherited_boxed_5296_: u8 = 0;
    let mut v_res_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inherited_boxed_5296_ = (crate::leanh::lean_unbox(v_inherited_5289_) as u8);
    v_res_5297_ = l_Lake_Dependency_materialize(
        v_dep_5288_,
        v_inherited_boxed_5296_,
        v_lakeEnv_5290_,
        v_wsDir_5291_,
        v_relPkgsDir_5292_,
        v_relParentDir_5293_,
        v_a_5294_,
    );
    crate::leanh::lean_dec_ref(v_a_5294_);
    return v_res_5297_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(
    mut v_manifestEntry_5303_: *mut crate::leanh::LeanObject,
    mut v_wsDir_5304_: *mut crate::leanh::LeanObject,
    mut v_relPkgDir_5305_: *mut crate::leanh::LeanObject,
    mut v_remoteUrl_5306_: *mut crate::leanh::LeanObject,
    mut v_a_5307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: u8 = 0;
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: u8 = 0;
    let mut v___x_5328_: usize = 0;
    let mut v___x_5329_: usize = 0;
    let mut v___x_2400__overap_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5335_: u8 = 0;
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v___x_5340_: usize = 0;
    let mut v___x_5341_: usize = 0;
    let mut v___x_2410__overap_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5347_: u8 = 0;
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5351_: u8 = 0;
    let mut v_a_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut v_a_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5372_: u8 = 0;
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5376_: u8 = 0;
    let mut v_val_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: u8 = 0;
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: u8 = 0;
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: u8 = 0;
    let mut v___x_5397_: usize = 0;
    let mut v___x_5398_: usize = 0;
    let mut v___x_2466__overap_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v___x_5409_: usize = 0;
    let mut v___x_5410_: usize = 0;
    let mut v___x_2476__overap_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_relPkgDir_5305_);
                v_pkgDir_5314_ = l_Lake_joinRelative(v_wsDir_5304_, v_relPkgDir_5305_);
                v___x_5315_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once), _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
                crate::leanh::lean_inc_ref(v_pkgDir_5314_);
                v___x_5316_ = l_Lake_resolvePath(v_pkgDir_5314_);
                v___f_5317_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2;
                v___x_5390_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5391_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_5421_ = lean_string_utf8_byte_size(v___x_5316_);
                v___x_5422_ = lean_nat_dec_eq(v___x_5421_, v___x_5390_);
                if v___x_5422_ == 0 {
                    v___x_5423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5423_, 0, v___x_5316_);
                    v_val_5393_ = v___x_5423_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5316_);
                    v___x_5424_ = crate::leanh::lean_box(0);
                    v_val_5393_ = v___x_5424_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_5312_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5312_, 0, v___y_5310_);
                crate::leanh::lean_ctor_set(v___x_5312_, 1, v_relPkgDir_5305_);
                crate::leanh::lean_ctor_set(v___x_5312_, 2, v_remoteUrl_5306_);
                crate::leanh::lean_ctor_set(v___x_5312_, 3, v_a_5311_);
                crate::leanh::lean_ctor_set(v___x_5312_, 4, v_manifestEntry_5303_);
                v___x_5313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5313_, 0, v___x_5312_);
                return v___x_5313_;
            }
            2 => {
                v___x_5324_ = lean_array_get_size(v___y_5320_);
                v___x_5325_ = lean_nat_dec_lt(v___y_5319_, v___x_5324_);
                if v___x_5325_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_5322_);
                    v___y_5310_ = v___y_5321_;
                    v_a_5311_ = v_val_5323_;
                    state = 1;
                    continue;
                } else {
                    v___x_5326_ = crate::leanh::lean_box(0);
                    v___x_5327_ = lean_nat_dec_le(v___x_5324_, v___x_5324_);
                    if v___x_5327_ == 0 {
                        if v___x_5325_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_5322_);
                            v___y_5310_ = v___y_5321_;
                            v_a_5311_ = v_val_5323_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5328_ = 0usize;
                            v___x_5329_ = lean_usize_of_nat(v___x_5324_);
                            crate::leanh::lean_inc_ref(v___y_5320_);
                            v___x_2400__overap_5330_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___y_5322_,
                                    v___f_5317_,
                                    v___y_5320_,
                                    v___x_5328_,
                                    v___x_5329_,
                                    v___x_5326_,
                                );
                            crate::leanh::lean_inc_ref(v_a_5307_);
                            v___x_5331_ = crate::leanh::lean_apply_2(
                                v___x_2400__overap_5330_,
                                v_a_5307_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_5331_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5331_, 1);
                                v___y_5310_ = v___y_5321_;
                                v_a_5311_ = v_val_5323_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_val_5323_);
                                crate::leanh::lean_dec_ref(v___y_5321_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_5306_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_5305_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5303_);
                                v_a_5332_ = crate::leanh::lean_ctor_get(v___x_5331_, 0);
                                v_isSharedCheck_5339_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5331_)) as u8;
                                if v_isSharedCheck_5339_ == 0 {
                                    v___x_5334_ = v___x_5331_;
                                    v_isShared_5335_ = v_isSharedCheck_5339_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5332_);
                                    crate::leanh::lean_dec(v___x_5331_);
                                    v___x_5334_ = crate::leanh::lean_box(0);
                                    v_isShared_5335_ = v_isSharedCheck_5339_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5340_ = 0usize;
                        v___x_5341_ = lean_usize_of_nat(v___x_5324_);
                        crate::leanh::lean_inc_ref(v___y_5320_);
                        v___x_2410__overap_5342_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___y_5322_,
                                v___f_5317_,
                                v___y_5320_,
                                v___x_5340_,
                                v___x_5341_,
                                v___x_5326_,
                            );
                        crate::leanh::lean_inc_ref(v_a_5307_);
                        v___x_5343_ = crate::leanh::lean_apply_2(
                            v___x_2410__overap_5342_,
                            v_a_5307_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5343_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5343_, 1);
                            v___y_5310_ = v___y_5321_;
                            v_a_5311_ = v_val_5323_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_val_5323_);
                            crate::leanh::lean_dec_ref(v___y_5321_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_5306_);
                            crate::leanh::lean_dec_ref(v_relPkgDir_5305_);
                            crate::leanh::lean_dec_ref(v_manifestEntry_5303_);
                            v_a_5344_ = crate::leanh::lean_ctor_get(v___x_5343_, 0);
                            v_isSharedCheck_5351_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5343_)) as u8;
                            if v_isSharedCheck_5351_ == 0 {
                                v___x_5346_ = v___x_5343_;
                                v_isShared_5347_ = v_isSharedCheck_5351_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5344_);
                                crate::leanh::lean_dec(v___x_5343_);
                                v___x_5346_ = crate::leanh::lean_box(0);
                                v_isShared_5347_ = v_isSharedCheck_5351_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_5335_ == 0 {
                    v___x_5337_ = v___x_5334_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5332_);
                    v___x_5337_ = v_reuseFailAlloc_5338_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5337_;
            }
            5 => {
                if v_isShared_5347_ == 0 {
                    v___x_5349_ = v___x_5346_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
                    v___x_5349_ = v_reuseFailAlloc_5350_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5349_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_5353_) == 1 {
                    crate::leanh::lean_dec_ref(v_pkgDir_5314_);
                    v_manifestFile_x3f_5354_ =
                        crate::leanh::lean_ctor_get(v_manifestEntry_5303_, 3);
                    if crate::leanh::lean_obj_tag(v_manifestFile_x3f_5354_) == 1 {
                        v_val_5355_ = crate::leanh::lean_ctor_get(v_a_5353_, 0);
                        crate::leanh::lean_inc_n(v_val_5355_, 2);
                        crate::leanh::lean_dec_ref_known(v_a_5353_, 1);
                        v_val_5356_ = crate::leanh::lean_ctor_get(v_manifestFile_x3f_5354_, 0);
                        crate::leanh::lean_inc(v_val_5356_);
                        v___x_5357_ = l_Lake_joinRelative(v_val_5355_, v_val_5356_);
                        v___x_5358_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5359_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                        v___x_5360_ = l_Lake_Manifest_load(v___x_5357_);
                        if crate::leanh::lean_obj_tag(v___x_5360_) == 0 {
                            v_a_5361_ = crate::leanh::lean_ctor_get(v___x_5360_, 0);
                            v_isSharedCheck_5368_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5360_)) as u8;
                            if v_isSharedCheck_5368_ == 0 {
                                v___x_5363_ = v___x_5360_;
                                v_isShared_5364_ = v_isSharedCheck_5368_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5361_);
                                crate::leanh::lean_dec(v___x_5360_);
                                v___x_5363_ = crate::leanh::lean_box(0);
                                v_isShared_5364_ = v_isSharedCheck_5368_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_5369_ = crate::leanh::lean_ctor_get(v___x_5360_, 0);
                            v_isSharedCheck_5376_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5360_)) as u8;
                            if v_isSharedCheck_5376_ == 0 {
                                v___x_5371_ = v___x_5360_;
                                v_isShared_5372_ = v_isSharedCheck_5376_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5369_);
                                crate::leanh::lean_dec(v___x_5360_);
                                v___x_5371_ = crate::leanh::lean_box(0);
                                v_isShared_5372_ = v_isSharedCheck_5376_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_val_5377_ = crate::leanh::lean_ctor_get(v_a_5353_, 0);
                        crate::leanh::lean_inc(v_val_5377_);
                        crate::leanh::lean_dec_ref_known(v_a_5353_, 1);
                        v___x_5378_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1;
                        v___y_5310_ = v_val_5377_;
                        v_a_5311_ = v___x_5378_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5353_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_5306_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_5305_);
                    v_name_5379_ = crate::leanh::lean_ctor_get(v_manifestEntry_5303_, 0);
                    crate::leanh::lean_inc(v_name_5379_);
                    crate::leanh::lean_dec_ref(v_manifestEntry_5303_);
                    v___x_5380_ = 0;
                    v___x_5381_ = l_Lean_Name_toString(v_name_5379_, v___x_5380_);
                    v___x_5382_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_5383_ = lean_string_append(v___x_5381_, v___x_5382_);
                    v___x_5384_ = lean_string_append(v___x_5383_, v_pkgDir_5314_);
                    crate::leanh::lean_dec_ref(v_pkgDir_5314_);
                    v___x_5385_ = 3;
                    v___x_5386_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5386_, 0, v___x_5384_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5386_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5385_,
                    );
                    crate::leanh::lean_inc_ref(v_a_5307_);
                    v___x_5387_ = crate::leanh::lean_apply_2(
                        v_a_5307_,
                        v___x_5386_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_5388_ = crate::leanh::lean_box(0);
                    v___x_5389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5389_, 0, v___x_5388_);
                    return v___x_5389_;
                }
            }
            8 => {
                if v_isShared_5364_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5363_, 1);
                    v___x_5366_ = v___x_5363_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
                    v___x_5366_ = v_reuseFailAlloc_5367_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_5319_ = v___x_5358_;
                v___y_5320_ = v___x_5359_;
                v___y_5321_ = v_val_5355_;
                v___y_5322_ = v___x_5315_;
                v_val_5323_ = v___x_5366_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_5372_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5371_, 0);
                    v___x_5374_ = v___x_5371_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
                    v___x_5374_ = v_reuseFailAlloc_5375_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_5319_ = v___x_5358_;
                v___y_5320_ = v___x_5359_;
                v___y_5321_ = v_val_5355_;
                v___y_5322_ = v___x_5315_;
                v_val_5323_ = v___x_5374_;
                state = 2;
                continue;
            }
            12 => {
                v___x_5394_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once
                    ),
                    _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5,
                );
                if v___x_5394_ == 0 {
                    v_a_5353_ = v_val_5393_;
                    state = 7;
                    continue;
                } else {
                    v___x_5395_ = crate::leanh::lean_box(0);
                    v___x_5396_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_5396_ == 0 {
                        if v___x_5394_ == 0 {
                            v_a_5353_ = v_val_5393_;
                            state = 7;
                            continue;
                        } else {
                            v___x_5397_ = 0usize;
                            v___x_5398_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_2466__overap_5399_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_5315_,
                                    v___f_5317_,
                                    v___x_5391_,
                                    v___x_5397_,
                                    v___x_5398_,
                                    v___x_5395_,
                                );
                            crate::leanh::lean_inc_ref(v_a_5307_);
                            v___x_5400_ = crate::leanh::lean_apply_2(
                                v___x_2466__overap_5399_,
                                v_a_5307_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_5400_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5400_, 1);
                                v_a_5353_ = v_val_5393_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_5393_);
                                crate::leanh::lean_dec_ref(v_pkgDir_5314_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_5306_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_5305_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5303_);
                                v_a_5401_ = crate::leanh::lean_ctor_get(v___x_5400_, 0);
                                v_isSharedCheck_5408_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5400_)) as u8;
                                if v_isSharedCheck_5408_ == 0 {
                                    v___x_5403_ = v___x_5400_;
                                    v_isShared_5404_ = v_isSharedCheck_5408_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5401_);
                                    crate::leanh::lean_dec(v___x_5400_);
                                    v___x_5403_ = crate::leanh::lean_box(0);
                                    v_isShared_5404_ = v_isSharedCheck_5408_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5409_ = 0usize;
                        v___x_5410_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_2476__overap_5411_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_5315_,
                                v___f_5317_,
                                v___x_5391_,
                                v___x_5409_,
                                v___x_5410_,
                                v___x_5395_,
                            );
                        crate::leanh::lean_inc_ref(v_a_5307_);
                        v___x_5412_ = crate::leanh::lean_apply_2(
                            v___x_2476__overap_5411_,
                            v_a_5307_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5412_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5412_, 1);
                            v_a_5353_ = v_val_5393_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_5393_);
                            crate::leanh::lean_dec_ref(v_pkgDir_5314_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_5306_);
                            crate::leanh::lean_dec_ref(v_relPkgDir_5305_);
                            crate::leanh::lean_dec_ref(v_manifestEntry_5303_);
                            v_a_5413_ = crate::leanh::lean_ctor_get(v___x_5412_, 0);
                            v_isSharedCheck_5420_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5412_)) as u8;
                            if v_isSharedCheck_5420_ == 0 {
                                v___x_5415_ = v___x_5412_;
                                v_isShared_5416_ = v_isSharedCheck_5420_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5413_);
                                crate::leanh::lean_dec(v___x_5412_);
                                v___x_5415_ = crate::leanh::lean_box(0);
                                v_isShared_5416_ = v_isSharedCheck_5420_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            13 => {
                if v_isShared_5404_ == 0 {
                    v___x_5406_ = v___x_5403_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
                    v___x_5406_ = v_reuseFailAlloc_5407_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5406_;
            }
            15 => {
                if v_isShared_5416_ == 0 {
                    v___x_5418_ = v___x_5415_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
                    v___x_5418_ = v_reuseFailAlloc_5419_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___boxed(
    mut v_manifestEntry_5425_: *mut crate::leanh::LeanObject,
    mut v_wsDir_5426_: *mut crate::leanh::LeanObject,
    mut v_relPkgDir_5427_: *mut crate::leanh::LeanObject,
    mut v_remoteUrl_5428_: *mut crate::leanh::LeanObject,
    mut v_a_5429_: *mut crate::leanh::LeanObject,
    mut v_a_5430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5431_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(
        v_manifestEntry_5425_,
        v_wsDir_5426_,
        v_relPkgDir_5427_,
        v_remoteUrl_5428_,
        v_a_5429_,
    );
    crate::leanh::lean_dec_ref(v_a_5429_);
    return v_res_5431_;
}
pub unsafe fn l_Lake_PackageEntry_materialize(
    mut v_manifestEntry_5433_: *mut crate::leanh::LeanObject,
    mut v_lakeEnv_5434_: *mut crate::leanh::LeanObject,
    mut v_wsDir_5435_: *mut crate::leanh::LeanObject,
    mut v_relPkgsDir_5436_: *mut crate::leanh::LeanObject,
    mut v_a_5437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: u8 = 0;
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: u8 = 0;
    let mut v___x_5458_: usize = 0;
    let mut v___x_5459_: usize = 0;
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5464_: u8 = 0;
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v___x_5469_: usize = 0;
    let mut v___x_5470_: usize = 0;
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5475_: u8 = 0;
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut v_src_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5486_: u8 = 0;
    let mut v_pkgDir_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: u8 = 0;
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: u8 = 0;
    let mut v___x_5506_: usize = 0;
    let mut v___x_5507_: usize = 0;
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5512_: u8 = 0;
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5516_: u8 = 0;
    let mut v___x_5517_: usize = 0;
    let mut v___x_5518_: usize = 0;
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5523_: u8 = 0;
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5527_: u8 = 0;
    let mut v_a_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5539_: u8 = 0;
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5543_: u8 = 0;
    let mut v_a_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5547_: u8 = 0;
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5551_: u8 = 0;
    let mut v_val_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: u8 = 0;
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: u8 = 0;
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: u8 = 0;
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: u8 = 0;
    let mut v___x_5571_: usize = 0;
    let mut v___x_5572_: usize = 0;
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5577_: u8 = 0;
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut v___x_5582_: usize = 0;
    let mut v___x_5583_: usize = 0;
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5588_: u8 = 0;
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5592_: u8 = 0;
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v_name_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rev_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subDir_x3f_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: u8 = 0;
    let mut v_sname_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5620_: u8 = 0;
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5624_: u8 = 0;
    let mut v_a_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5632_: u8 = 0;
    let mut v_val_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: u8 = 0;
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: u8 = 0;
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: u8 = 0;
    let mut v___x_5655_: usize = 0;
    let mut v___x_5656_: usize = 0;
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5661_: u8 = 0;
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5665_: u8 = 0;
    let mut v___x_5666_: usize = 0;
    let mut v___x_5667_: usize = 0;
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5676_: u8 = 0;
    let mut v___y_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: u8 = 0;
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relGitDir_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gitDir_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5708_: u8 = 0;
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5712_: u8 = 0;
    let mut v___y_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5720_: u8 = 0;
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut v_a_5726_: u8 = 0;
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: u8 = 0;
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5738_: u8 = 0;
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: u8 = 0;
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: u8 = 0;
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5749_: u8 = 0;
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5753_: u8 = 0;
    let mut v___x_5754_: usize = 0;
    let mut v___x_5755_: usize = 0;
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5760_: u8 = 0;
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5764_: u8 = 0;
    let mut v___y_5766_: u8 = 0;
    let mut v_a_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: u8 = 0;
    let mut v_pkgUrlMap_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: u8 = 0;
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: u8 = 0;
    let mut v_pkgUrlMap_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: u8 = 0;
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: u8 = 0;
    let mut v___x_5788_: usize = 0;
    let mut v___x_5789_: usize = 0;
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5794_: u8 = 0;
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5798_: u8 = 0;
    let mut v___x_5799_: usize = 0;
    let mut v___x_5800_: usize = 0;
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5805_: u8 = 0;
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5809_: u8 = 0;
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: u8 = 0;
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: u8 = 0;
    let mut v___x_5814_: usize = 0;
    let mut v___x_5815_: usize = 0;
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5820_: u8 = 0;
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5824_: u8 = 0;
    let mut v___x_5825_: usize = 0;
    let mut v___x_5826_: usize = 0;
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5831_: u8 = 0;
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_src_5480_ = crate::leanh::lean_ctor_get(v_manifestEntry_5433_, 4);
                crate::leanh::lean_inc_ref(v_src_5480_);
                if crate::leanh::lean_obj_tag(v_src_5480_) == 0 {
                    crate::leanh::lean_dec_ref(v_relPkgsDir_5436_);
                    v_name_5481_ = crate::leanh::lean_ctor_get(v_manifestEntry_5433_, 0);
                    v_manifestFile_x3f_5482_ =
                        crate::leanh::lean_ctor_get(v_manifestEntry_5433_, 3);
                    v_dir_5483_ = crate::leanh::lean_ctor_get(v_src_5480_, 0);
                    v_isSharedCheck_5597_ = (!crate::leanh::lean_is_exclusive(v_src_5480_)) as u8;
                    if v_isSharedCheck_5597_ == 0 {
                        v___x_5485_ = v_src_5480_;
                        v_isShared_5486_ = v_isSharedCheck_5597_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_dir_5483_);
                        crate::leanh::lean_dec(v_src_5480_);
                        v___x_5485_ = crate::leanh::lean_box(0);
                        v_isShared_5486_ = v_isSharedCheck_5597_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_name_5598_ = crate::leanh::lean_ctor_get(v_manifestEntry_5433_, 0);
                    v_manifestFile_x3f_5599_ =
                        crate::leanh::lean_ctor_get(v_manifestEntry_5433_, 3);
                    v_url_5600_ = crate::leanh::lean_ctor_get(v_src_5480_, 0);
                    crate::leanh::lean_inc_ref(v_url_5600_);
                    v_rev_5601_ = crate::leanh::lean_ctor_get(v_src_5480_, 1);
                    crate::leanh::lean_inc_ref(v_rev_5601_);
                    v_subDir_x3f_5602_ = crate::leanh::lean_ctor_get(v_src_5480_, 3);
                    crate::leanh::lean_inc(v_subDir_x3f_5602_);
                    crate::leanh::lean_dec_ref_known(v_src_5480_, 4);
                    v___x_5603_ = 0;
                    crate::leanh::lean_inc(v_name_5598_);
                    v_sname_5604_ = l_Lean_Name_toString(v_name_5598_, v___x_5603_);
                    crate::leanh::lean_inc_ref(v_sname_5604_);
                    v_relGitDir_5695_ = l_Lake_joinRelative(v_relPkgsDir_5436_, v_sname_5604_);
                    crate::leanh::lean_inc_ref(v_relGitDir_5695_);
                    crate::leanh::lean_inc_ref(v_wsDir_5435_);
                    v_gitDir_5700_ = l_Lake_joinRelative(v_wsDir_5435_, v_relGitDir_5695_);
                    v___x_5777_ = l_System_FilePath_isDir(v_gitDir_5700_);
                    v___x_5810_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_5811_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
                    if v___x_5811_ == 0 {
                        state = 51;
                        continue;
                    } else {
                        v___x_5812_ = crate::leanh::lean_box(0);
                        v___x_5813_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                        if v___x_5813_ == 0 {
                            if v___x_5811_ == 0 {
                                state = 51;
                                continue;
                            } else {
                                v___x_5814_ = 0usize;
                                v___x_5815_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                v___x_5816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5810_, v___x_5814_, v___x_5815_, v___x_5812_, v_a_5437_);
                                if crate::leanh::lean_obj_tag(v___x_5816_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5816_, 1);
                                    state = 51;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_gitDir_5700_);
                                    crate::leanh::lean_dec_ref(v_relGitDir_5695_);
                                    crate::leanh::lean_dec_ref(v_sname_5604_);
                                    crate::leanh::lean_dec(v_subDir_x3f_5602_);
                                    crate::leanh::lean_dec_ref(v_rev_5601_);
                                    crate::leanh::lean_dec_ref(v_url_5600_);
                                    crate::leanh::lean_dec_ref(v_wsDir_5435_);
                                    crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                    v_a_5817_ = crate::leanh::lean_ctor_get(v___x_5816_, 0);
                                    v_isSharedCheck_5824_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5816_)) as u8;
                                    if v_isSharedCheck_5824_ == 0 {
                                        v___x_5819_ = v___x_5816_;
                                        v_isShared_5820_ = v_isSharedCheck_5824_;
                                        state = 56;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5817_);
                                        crate::leanh::lean_dec(v___x_5816_);
                                        v___x_5819_ = crate::leanh::lean_box(0);
                                        v_isShared_5820_ = v_isSharedCheck_5824_;
                                        state = 56;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_5825_ = 0usize;
                            v___x_5826_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_5827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5810_, v___x_5825_, v___x_5826_, v___x_5812_, v_a_5437_);
                            if crate::leanh::lean_obj_tag(v___x_5827_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5827_, 1);
                                state = 51;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_gitDir_5700_);
                                crate::leanh::lean_dec_ref(v_relGitDir_5695_);
                                crate::leanh::lean_dec_ref(v_sname_5604_);
                                crate::leanh::lean_dec(v_subDir_x3f_5602_);
                                crate::leanh::lean_dec_ref(v_rev_5601_);
                                crate::leanh::lean_dec_ref(v_url_5600_);
                                crate::leanh::lean_dec_ref(v_wsDir_5435_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5828_ = crate::leanh::lean_ctor_get(v___x_5827_, 0);
                                v_isSharedCheck_5835_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5827_)) as u8;
                                if v_isSharedCheck_5835_ == 0 {
                                    v___x_5830_ = v___x_5827_;
                                    v_isShared_5831_ = v_isSharedCheck_5835_;
                                    state = 58;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5828_);
                                    crate::leanh::lean_dec(v___x_5827_);
                                    v___x_5830_ = crate::leanh::lean_box(0);
                                    v_isShared_5831_ = v_isSharedCheck_5835_;
                                    state = 58;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5444_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5444_, 0, v___y_5441_);
                crate::leanh::lean_ctor_set(v___x_5444_, 1, v___y_5442_);
                crate::leanh::lean_ctor_set(v___x_5444_, 2, v___y_5440_);
                crate::leanh::lean_ctor_set(v___x_5444_, 3, v_a_5443_);
                crate::leanh::lean_ctor_set(v___x_5444_, 4, v_manifestEntry_5433_);
                v___x_5445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5445_, 0, v___x_5444_);
                return v___x_5445_;
            }
            2 => {
                v___x_5454_ = lean_array_get_size(v___y_5452_);
                v___x_5455_ = lean_nat_dec_lt(v___y_5450_, v___x_5454_);
                if v___x_5455_ == 0 {
                    v___y_5440_ = v___y_5448_;
                    v___y_5441_ = v___y_5447_;
                    v___y_5442_ = v___y_5451_;
                    v_a_5443_ = v_val_5453_;
                    state = 1;
                    continue;
                } else {
                    v___x_5456_ = crate::leanh::lean_box(0);
                    v___x_5457_ = lean_nat_dec_le(v___x_5454_, v___x_5454_);
                    if v___x_5457_ == 0 {
                        if v___x_5455_ == 0 {
                            v___y_5440_ = v___y_5448_;
                            v___y_5441_ = v___y_5447_;
                            v___y_5442_ = v___y_5451_;
                            v_a_5443_ = v_val_5453_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5458_ = 0usize;
                            v___x_5459_ = lean_usize_of_nat(v___x_5454_);
                            v___x_5460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_5452_, v___x_5458_, v___x_5459_, v___x_5456_, v___y_5449_);
                            if crate::leanh::lean_obj_tag(v___x_5460_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5460_, 1);
                                v___y_5440_ = v___y_5448_;
                                v___y_5441_ = v___y_5447_;
                                v___y_5442_ = v___y_5451_;
                                v_a_5443_ = v_val_5453_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_val_5453_);
                                crate::leanh::lean_dec_ref(v___y_5451_);
                                crate::leanh::lean_dec_ref(v___y_5448_);
                                crate::leanh::lean_dec_ref(v___y_5447_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5461_ = crate::leanh::lean_ctor_get(v___x_5460_, 0);
                                v_isSharedCheck_5468_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5460_)) as u8;
                                if v_isSharedCheck_5468_ == 0 {
                                    v___x_5463_ = v___x_5460_;
                                    v_isShared_5464_ = v_isSharedCheck_5468_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5461_);
                                    crate::leanh::lean_dec(v___x_5460_);
                                    v___x_5463_ = crate::leanh::lean_box(0);
                                    v_isShared_5464_ = v_isSharedCheck_5468_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5469_ = 0usize;
                        v___x_5470_ = lean_usize_of_nat(v___x_5454_);
                        v___x_5471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_5452_, v___x_5469_, v___x_5470_, v___x_5456_, v___y_5449_);
                        if crate::leanh::lean_obj_tag(v___x_5471_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5471_, 1);
                            v___y_5440_ = v___y_5448_;
                            v___y_5441_ = v___y_5447_;
                            v___y_5442_ = v___y_5451_;
                            v_a_5443_ = v_val_5453_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_val_5453_);
                            crate::leanh::lean_dec_ref(v___y_5451_);
                            crate::leanh::lean_dec_ref(v___y_5448_);
                            crate::leanh::lean_dec_ref(v___y_5447_);
                            crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5472_ = crate::leanh::lean_ctor_get(v___x_5471_, 0);
                            v_isSharedCheck_5479_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5471_)) as u8;
                            if v_isSharedCheck_5479_ == 0 {
                                v___x_5474_ = v___x_5471_;
                                v_isShared_5475_ = v_isSharedCheck_5479_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5472_);
                                crate::leanh::lean_dec(v___x_5471_);
                                v___x_5474_ = crate::leanh::lean_box(0);
                                v_isShared_5475_ = v_isSharedCheck_5479_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_5464_ == 0 {
                    v___x_5466_ = v___x_5463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5461_);
                    v___x_5466_ = v_reuseFailAlloc_5467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5466_;
            }
            5 => {
                if v_isShared_5475_ == 0 {
                    v___x_5477_ = v___x_5474_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5478_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
                    v___x_5477_ = v_reuseFailAlloc_5478_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5477_;
            }
            7 => {
                crate::leanh::lean_inc_ref(v_dir_5483_);
                v_pkgDir_5487_ = l_Lake_joinRelative(v_wsDir_5435_, v_dir_5483_);
                crate::leanh::lean_inc_ref(v_pkgDir_5487_);
                v___x_5488_ = l_Lake_resolvePath(v_pkgDir_5487_);
                v___x_5489_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                v___x_5564_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5565_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_5593_ = lean_string_utf8_byte_size(v___x_5488_);
                v___x_5594_ = lean_nat_dec_eq(v___x_5593_, v___x_5564_);
                if v___x_5594_ == 0 {
                    v___x_5595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5595_, 0, v___x_5488_);
                    v_val_5567_ = v___x_5595_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5488_);
                    v___x_5596_ = crate::leanh::lean_box(0);
                    v_val_5567_ = v___x_5596_;
                    state = 20;
                    continue;
                }
            }
            8 => {
                v___x_5493_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5493_, 0, v___y_5491_);
                crate::leanh::lean_ctor_set(v___x_5493_, 1, v_dir_5483_);
                crate::leanh::lean_ctor_set(v___x_5493_, 2, v___x_5489_);
                crate::leanh::lean_ctor_set(v___x_5493_, 3, v_a_5492_);
                crate::leanh::lean_ctor_set(v___x_5493_, 4, v_manifestEntry_5433_);
                if v_isShared_5486_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5485_, 0, v___x_5493_);
                    v___x_5495_ = v___x_5485_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5493_);
                    v___x_5495_ = v_reuseFailAlloc_5496_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5495_;
            }
            10 => {
                v___x_5502_ = lean_array_get_size(v___y_5499_);
                v___x_5503_ = lean_nat_dec_lt(v___y_5498_, v___x_5502_);
                if v___x_5503_ == 0 {
                    v___y_5491_ = v___y_5500_;
                    v_a_5492_ = v_val_5501_;
                    state = 8;
                    continue;
                } else {
                    v___x_5504_ = crate::leanh::lean_box(0);
                    v___x_5505_ = lean_nat_dec_le(v___x_5502_, v___x_5502_);
                    if v___x_5505_ == 0 {
                        if v___x_5503_ == 0 {
                            v___y_5491_ = v___y_5500_;
                            v_a_5492_ = v_val_5501_;
                            state = 8;
                            continue;
                        } else {
                            v___x_5506_ = 0usize;
                            v___x_5507_ = lean_usize_of_nat(v___x_5502_);
                            v___x_5508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_5499_, v___x_5506_, v___x_5507_, v___x_5504_, v_a_5437_);
                            if crate::leanh::lean_obj_tag(v___x_5508_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5508_, 1);
                                v___y_5491_ = v___y_5500_;
                                v_a_5492_ = v_val_5501_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_val_5501_);
                                crate::leanh::lean_dec_ref(v___y_5500_);
                                crate::leanh::lean_del_object(v___x_5485_);
                                crate::leanh::lean_dec_ref(v_dir_5483_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5509_ = crate::leanh::lean_ctor_get(v___x_5508_, 0);
                                v_isSharedCheck_5516_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5508_)) as u8;
                                if v_isSharedCheck_5516_ == 0 {
                                    v___x_5511_ = v___x_5508_;
                                    v_isShared_5512_ = v_isSharedCheck_5516_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5509_);
                                    crate::leanh::lean_dec(v___x_5508_);
                                    v___x_5511_ = crate::leanh::lean_box(0);
                                    v_isShared_5512_ = v_isSharedCheck_5516_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5517_ = 0usize;
                        v___x_5518_ = lean_usize_of_nat(v___x_5502_);
                        v___x_5519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_5499_, v___x_5517_, v___x_5518_, v___x_5504_, v_a_5437_);
                        if crate::leanh::lean_obj_tag(v___x_5519_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5519_, 1);
                            v___y_5491_ = v___y_5500_;
                            v_a_5492_ = v_val_5501_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_val_5501_);
                            crate::leanh::lean_dec_ref(v___y_5500_);
                            crate::leanh::lean_del_object(v___x_5485_);
                            crate::leanh::lean_dec_ref(v_dir_5483_);
                            crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5520_ = crate::leanh::lean_ctor_get(v___x_5519_, 0);
                            v_isSharedCheck_5527_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5519_)) as u8;
                            if v_isSharedCheck_5527_ == 0 {
                                v___x_5522_ = v___x_5519_;
                                v_isShared_5523_ = v_isSharedCheck_5527_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5520_);
                                crate::leanh::lean_dec(v___x_5519_);
                                v___x_5522_ = crate::leanh::lean_box(0);
                                v_isShared_5523_ = v_isSharedCheck_5527_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                }
            }
            11 => {
                if v_isShared_5512_ == 0 {
                    v___x_5514_ = v___x_5511_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5509_);
                    v___x_5514_ = v_reuseFailAlloc_5515_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5514_;
            }
            13 => {
                if v_isShared_5523_ == 0 {
                    v___x_5525_ = v___x_5522_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_a_5520_);
                    v___x_5525_ = v_reuseFailAlloc_5526_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5525_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v_a_5529_) == 1 {
                    crate::leanh::lean_dec_ref(v_pkgDir_5487_);
                    if crate::leanh::lean_obj_tag(v_manifestFile_x3f_5482_) == 1 {
                        v_val_5530_ = crate::leanh::lean_ctor_get(v_a_5529_, 0);
                        crate::leanh::lean_inc_n(v_val_5530_, 2);
                        crate::leanh::lean_dec_ref_known(v_a_5529_, 1);
                        v_val_5531_ = crate::leanh::lean_ctor_get(v_manifestFile_x3f_5482_, 0);
                        crate::leanh::lean_inc(v_val_5531_);
                        v___x_5532_ = l_Lake_joinRelative(v_val_5530_, v_val_5531_);
                        v___x_5533_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5534_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                        v___x_5535_ = l_Lake_Manifest_load(v___x_5532_);
                        if crate::leanh::lean_obj_tag(v___x_5535_) == 0 {
                            v_a_5536_ = crate::leanh::lean_ctor_get(v___x_5535_, 0);
                            v_isSharedCheck_5543_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5535_)) as u8;
                            if v_isSharedCheck_5543_ == 0 {
                                v___x_5538_ = v___x_5535_;
                                v_isShared_5539_ = v_isSharedCheck_5543_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5536_);
                                crate::leanh::lean_dec(v___x_5535_);
                                v___x_5538_ = crate::leanh::lean_box(0);
                                v_isShared_5539_ = v_isSharedCheck_5543_;
                                state = 16;
                                continue;
                            }
                        } else {
                            v_a_5544_ = crate::leanh::lean_ctor_get(v___x_5535_, 0);
                            v_isSharedCheck_5551_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5535_)) as u8;
                            if v_isSharedCheck_5551_ == 0 {
                                v___x_5546_ = v___x_5535_;
                                v_isShared_5547_ = v_isSharedCheck_5551_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5544_);
                                crate::leanh::lean_dec(v___x_5535_);
                                v___x_5546_ = crate::leanh::lean_box(0);
                                v_isShared_5547_ = v_isSharedCheck_5551_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        v_val_5552_ = crate::leanh::lean_ctor_get(v_a_5529_, 0);
                        crate::leanh::lean_inc(v_val_5552_);
                        crate::leanh::lean_dec_ref_known(v_a_5529_, 1);
                        v___x_5553_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1;
                        v___y_5491_ = v_val_5552_;
                        v_a_5492_ = v___x_5553_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_name_5481_);
                    crate::leanh::lean_dec(v_a_5529_);
                    crate::leanh::lean_del_object(v___x_5485_);
                    crate::leanh::lean_dec_ref(v_dir_5483_);
                    crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                    v___x_5554_ = 0;
                    v___x_5555_ = l_Lean_Name_toString(v_name_5481_, v___x_5554_);
                    v___x_5556_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_5557_ = lean_string_append(v___x_5555_, v___x_5556_);
                    v___x_5558_ = lean_string_append(v___x_5557_, v_pkgDir_5487_);
                    crate::leanh::lean_dec_ref(v_pkgDir_5487_);
                    v___x_5559_ = 3;
                    v___x_5560_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5560_, 0, v___x_5558_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5560_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5559_,
                    );
                    crate::leanh::lean_inc_ref(v_a_5437_);
                    v___x_5561_ = crate::leanh::lean_apply_2(
                        v_a_5437_,
                        v___x_5560_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_5562_ = crate::leanh::lean_box(0);
                    v___x_5563_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5563_, 0, v___x_5562_);
                    return v___x_5563_;
                }
            }
            16 => {
                if v_isShared_5539_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5538_, 1);
                    v___x_5541_ = v___x_5538_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_a_5536_);
                    v___x_5541_ = v_reuseFailAlloc_5542_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_5498_ = v___x_5533_;
                v___y_5499_ = v___x_5534_;
                v___y_5500_ = v_val_5530_;
                v_val_5501_ = v___x_5541_;
                state = 10;
                continue;
            }
            18 => {
                if v_isShared_5547_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5546_, 0);
                    v___x_5549_ = v___x_5546_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5550_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
                    v___x_5549_ = v_reuseFailAlloc_5550_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_5498_ = v___x_5533_;
                v___y_5499_ = v___x_5534_;
                v___y_5500_ = v_val_5530_;
                v_val_5501_ = v___x_5549_;
                state = 10;
                continue;
            }
            20 => {
                v___x_5568_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once
                    ),
                    _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5,
                );
                if v___x_5568_ == 0 {
                    v_a_5529_ = v_val_5567_;
                    state = 15;
                    continue;
                } else {
                    v___x_5569_ = crate::leanh::lean_box(0);
                    v___x_5570_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_5570_ == 0 {
                        if v___x_5568_ == 0 {
                            v_a_5529_ = v_val_5567_;
                            state = 15;
                            continue;
                        } else {
                            v___x_5571_ = 0usize;
                            v___x_5572_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_5573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5565_, v___x_5571_, v___x_5572_, v___x_5569_, v_a_5437_);
                            if crate::leanh::lean_obj_tag(v___x_5573_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5573_, 1);
                                v_a_5529_ = v_val_5567_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_5567_);
                                crate::leanh::lean_dec_ref(v_pkgDir_5487_);
                                crate::leanh::lean_del_object(v___x_5485_);
                                crate::leanh::lean_dec_ref(v_dir_5483_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5574_ = crate::leanh::lean_ctor_get(v___x_5573_, 0);
                                v_isSharedCheck_5581_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5573_)) as u8;
                                if v_isSharedCheck_5581_ == 0 {
                                    v___x_5576_ = v___x_5573_;
                                    v_isShared_5577_ = v_isSharedCheck_5581_;
                                    state = 21;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5574_);
                                    crate::leanh::lean_dec(v___x_5573_);
                                    v___x_5576_ = crate::leanh::lean_box(0);
                                    v_isShared_5577_ = v_isSharedCheck_5581_;
                                    state = 21;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5582_ = 0usize;
                        v___x_5583_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_5584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5565_, v___x_5582_, v___x_5583_, v___x_5569_, v_a_5437_);
                        if crate::leanh::lean_obj_tag(v___x_5584_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5584_, 1);
                            v_a_5529_ = v_val_5567_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_5567_);
                            crate::leanh::lean_dec_ref(v_pkgDir_5487_);
                            crate::leanh::lean_del_object(v___x_5485_);
                            crate::leanh::lean_dec_ref(v_dir_5483_);
                            crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5585_ = crate::leanh::lean_ctor_get(v___x_5584_, 0);
                            v_isSharedCheck_5592_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5584_)) as u8;
                            if v_isSharedCheck_5592_ == 0 {
                                v___x_5587_ = v___x_5584_;
                                v_isShared_5588_ = v_isSharedCheck_5592_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5585_);
                                crate::leanh::lean_dec(v___x_5584_);
                                v___x_5587_ = crate::leanh::lean_box(0);
                                v_isShared_5588_ = v_isSharedCheck_5592_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                }
            }
            21 => {
                if v_isShared_5577_ == 0 {
                    v___x_5579_ = v___x_5576_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
                    v___x_5579_ = v_reuseFailAlloc_5580_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5579_;
            }
            23 => {
                if v_isShared_5588_ == 0 {
                    v___x_5590_ = v___x_5587_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
                    v___x_5590_ = v_reuseFailAlloc_5591_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5590_;
            }
            25 => {
                if crate::leanh::lean_obj_tag(v_a_5610_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_5607_);
                    crate::leanh::lean_dec_ref(v_sname_5604_);
                    if crate::leanh::lean_obj_tag(v_manifestFile_x3f_5599_) == 1 {
                        v_val_5611_ = crate::leanh::lean_ctor_get(v_a_5610_, 0);
                        crate::leanh::lean_inc_n(v_val_5611_, 2);
                        crate::leanh::lean_dec_ref_known(v_a_5610_, 1);
                        v_val_5612_ = crate::leanh::lean_ctor_get(v_manifestFile_x3f_5599_, 0);
                        crate::leanh::lean_inc(v_val_5612_);
                        v___x_5613_ = l_Lake_joinRelative(v_val_5611_, v_val_5612_);
                        v___x_5614_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5615_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                        v___x_5616_ = l_Lake_Manifest_load(v___x_5613_);
                        if crate::leanh::lean_obj_tag(v___x_5616_) == 0 {
                            v_a_5617_ = crate::leanh::lean_ctor_get(v___x_5616_, 0);
                            v_isSharedCheck_5624_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5616_)) as u8;
                            if v_isSharedCheck_5624_ == 0 {
                                v___x_5619_ = v___x_5616_;
                                v_isShared_5620_ = v_isSharedCheck_5624_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5617_);
                                crate::leanh::lean_dec(v___x_5616_);
                                v___x_5619_ = crate::leanh::lean_box(0);
                                v_isShared_5620_ = v_isSharedCheck_5624_;
                                state = 26;
                                continue;
                            }
                        } else {
                            v_a_5625_ = crate::leanh::lean_ctor_get(v___x_5616_, 0);
                            v_isSharedCheck_5632_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5616_)) as u8;
                            if v_isSharedCheck_5632_ == 0 {
                                v___x_5627_ = v___x_5616_;
                                v_isShared_5628_ = v_isSharedCheck_5632_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5625_);
                                crate::leanh::lean_dec(v___x_5616_);
                                v___x_5627_ = crate::leanh::lean_box(0);
                                v_isShared_5628_ = v_isSharedCheck_5632_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        v_val_5633_ = crate::leanh::lean_ctor_get(v_a_5610_, 0);
                        crate::leanh::lean_inc(v_val_5633_);
                        crate::leanh::lean_dec_ref_known(v_a_5610_, 1);
                        v___x_5634_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1;
                        v___y_5440_ = v___y_5606_;
                        v___y_5441_ = v_val_5633_;
                        v___y_5442_ = v___y_5609_;
                        v_a_5443_ = v___x_5634_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5610_);
                    crate::leanh::lean_dec_ref(v___y_5609_);
                    crate::leanh::lean_dec_ref(v___y_5606_);
                    crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                    v___x_5635_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_5636_ = lean_string_append(v_sname_5604_, v___x_5635_);
                    v___x_5637_ = lean_string_append(v___x_5636_, v___y_5607_);
                    crate::leanh::lean_dec_ref(v___y_5607_);
                    v___x_5638_ = 3;
                    v___x_5639_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5639_, 0, v___x_5637_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5639_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5638_,
                    );
                    crate::leanh::lean_inc_ref(v___y_5608_);
                    v___x_5640_ = crate::leanh::lean_apply_2(
                        v___y_5608_,
                        v___x_5639_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_5641_ = crate::leanh::lean_box(0);
                    v___x_5642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5642_, 0, v___x_5641_);
                    return v___x_5642_;
                }
            }
            26 => {
                if v_isShared_5620_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5619_, 1);
                    v___x_5622_ = v___x_5619_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
                    v___x_5622_ = v_reuseFailAlloc_5623_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___y_5447_ = v_val_5611_;
                v___y_5448_ = v___y_5606_;
                v___y_5449_ = v___y_5608_;
                v___y_5450_ = v___x_5614_;
                v___y_5451_ = v___y_5609_;
                v___y_5452_ = v___x_5615_;
                v_val_5453_ = v___x_5622_;
                state = 2;
                continue;
            }
            28 => {
                if v_isShared_5628_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5627_, 0);
                    v___x_5630_ = v___x_5627_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_a_5625_);
                    v___x_5630_ = v_reuseFailAlloc_5631_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___y_5447_ = v_val_5611_;
                v___y_5448_ = v___y_5606_;
                v___y_5449_ = v___y_5608_;
                v___y_5450_ = v___x_5614_;
                v___y_5451_ = v___y_5609_;
                v___y_5452_ = v___x_5615_;
                v_val_5453_ = v___x_5630_;
                state = 2;
                continue;
            }
            30 => {
                v___x_5651_ = lean_array_get_size(v___y_5644_);
                v___x_5652_ = lean_nat_dec_lt(v___y_5648_, v___x_5651_);
                if v___x_5652_ == 0 {
                    v___y_5606_ = v___y_5645_;
                    v___y_5607_ = v___y_5646_;
                    v___y_5608_ = v___y_5647_;
                    v___y_5609_ = v___y_5649_;
                    v_a_5610_ = v_val_5650_;
                    state = 25;
                    continue;
                } else {
                    v___x_5653_ = crate::leanh::lean_box(0);
                    v___x_5654_ = lean_nat_dec_le(v___x_5651_, v___x_5651_);
                    if v___x_5654_ == 0 {
                        if v___x_5652_ == 0 {
                            v___y_5606_ = v___y_5645_;
                            v___y_5607_ = v___y_5646_;
                            v___y_5608_ = v___y_5647_;
                            v___y_5609_ = v___y_5649_;
                            v_a_5610_ = v_val_5650_;
                            state = 25;
                            continue;
                        } else {
                            v___x_5655_ = 0usize;
                            v___x_5656_ = lean_usize_of_nat(v___x_5651_);
                            v___x_5657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_5644_, v___x_5655_, v___x_5656_, v___x_5653_, v___y_5647_);
                            if crate::leanh::lean_obj_tag(v___x_5657_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5657_, 1);
                                v___y_5606_ = v___y_5645_;
                                v___y_5607_ = v___y_5646_;
                                v___y_5608_ = v___y_5647_;
                                v___y_5609_ = v___y_5649_;
                                v_a_5610_ = v_val_5650_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_5650_);
                                crate::leanh::lean_dec_ref(v___y_5649_);
                                crate::leanh::lean_dec_ref(v___y_5646_);
                                crate::leanh::lean_dec_ref(v___y_5645_);
                                crate::leanh::lean_dec_ref(v_sname_5604_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5658_ = crate::leanh::lean_ctor_get(v___x_5657_, 0);
                                v_isSharedCheck_5665_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5657_)) as u8;
                                if v_isSharedCheck_5665_ == 0 {
                                    v___x_5660_ = v___x_5657_;
                                    v_isShared_5661_ = v_isSharedCheck_5665_;
                                    state = 31;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5658_);
                                    crate::leanh::lean_dec(v___x_5657_);
                                    v___x_5660_ = crate::leanh::lean_box(0);
                                    v_isShared_5661_ = v_isSharedCheck_5665_;
                                    state = 31;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5666_ = 0usize;
                        v___x_5667_ = lean_usize_of_nat(v___x_5651_);
                        v___x_5668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_5644_, v___x_5666_, v___x_5667_, v___x_5653_, v___y_5647_);
                        if crate::leanh::lean_obj_tag(v___x_5668_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5668_, 1);
                            v___y_5606_ = v___y_5645_;
                            v___y_5607_ = v___y_5646_;
                            v___y_5608_ = v___y_5647_;
                            v___y_5609_ = v___y_5649_;
                            v_a_5610_ = v_val_5650_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_5650_);
                            crate::leanh::lean_dec_ref(v___y_5649_);
                            crate::leanh::lean_dec_ref(v___y_5646_);
                            crate::leanh::lean_dec_ref(v___y_5645_);
                            crate::leanh::lean_dec_ref(v_sname_5604_);
                            crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5669_ = crate::leanh::lean_ctor_get(v___x_5668_, 0);
                            v_isSharedCheck_5676_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5668_)) as u8;
                            if v_isSharedCheck_5676_ == 0 {
                                v___x_5671_ = v___x_5668_;
                                v_isShared_5672_ = v_isSharedCheck_5676_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5669_);
                                crate::leanh::lean_dec(v___x_5668_);
                                v___x_5671_ = crate::leanh::lean_box(0);
                                v_isShared_5672_ = v_isSharedCheck_5676_;
                                state = 33;
                                continue;
                            }
                        }
                    }
                }
            }
            31 => {
                if v_isShared_5661_ == 0 {
                    v___x_5663_ = v___x_5660_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5664_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
                    v___x_5663_ = v_reuseFailAlloc_5664_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5663_;
            }
            33 => {
                if v_isShared_5672_ == 0 {
                    v___x_5674_ = v___x_5671_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
                    v___x_5674_ = v_reuseFailAlloc_5675_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5674_;
            }
            35 => {
                crate::leanh::lean_inc_ref(v___y_5679_);
                v_pkgDir_5681_ = l_Lake_joinRelative(v_wsDir_5435_, v___y_5679_);
                crate::leanh::lean_inc_ref(v_pkgDir_5681_);
                v___x_5682_ = l_Lake_resolvePath(v_pkgDir_5681_);
                v___x_5683_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5684_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_5685_ = lean_string_utf8_byte_size(v___x_5682_);
                v___x_5686_ = lean_nat_dec_eq(v___x_5685_, v___x_5683_);
                if v___x_5686_ == 0 {
                    v___x_5687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5687_, 0, v___x_5682_);
                    v___y_5644_ = v___x_5684_;
                    v___y_5645_ = v___y_5680_;
                    v___y_5646_ = v_pkgDir_5681_;
                    v___y_5647_ = v___y_5678_;
                    v___y_5648_ = v___x_5683_;
                    v___y_5649_ = v___y_5679_;
                    v_val_5650_ = v___x_5687_;
                    state = 30;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5682_);
                    v___x_5688_ = crate::leanh::lean_box(0);
                    v___y_5644_ = v___x_5684_;
                    v___y_5645_ = v___y_5680_;
                    v___y_5646_ = v_pkgDir_5681_;
                    v___y_5647_ = v___y_5678_;
                    v___y_5648_ = v___x_5683_;
                    v___y_5649_ = v___y_5679_;
                    v_val_5650_ = v___x_5688_;
                    state = 30;
                    continue;
                }
            }
            36 => {
                v___x_5692_ = l_Lake_Git_filterUrl_x3f(v_url_5600_);
                if crate::leanh::lean_obj_tag(v___x_5692_) == 0 {
                    v___x_5693_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                    v___y_5678_ = v___y_5690_;
                    v___y_5679_ = v___y_5691_;
                    v___y_5680_ = v___x_5693_;
                    state = 35;
                    continue;
                } else {
                    v_val_5694_ = crate::leanh::lean_ctor_get(v___x_5692_, 0);
                    crate::leanh::lean_inc(v_val_5694_);
                    crate::leanh::lean_dec_ref_known(v___x_5692_, 1);
                    v___y_5678_ = v___y_5690_;
                    v___y_5679_ = v___y_5691_;
                    v___y_5680_ = v_val_5694_;
                    state = 35;
                    continue;
                }
            }
            37 => {
                if crate::leanh::lean_obj_tag(v_subDir_x3f_5602_) == 0 {
                    v___y_5690_ = v___y_5697_;
                    v___y_5691_ = v_relGitDir_5695_;
                    state = 36;
                    continue;
                } else {
                    v_val_5698_ = crate::leanh::lean_ctor_get(v_subDir_x3f_5602_, 0);
                    crate::leanh::lean_inc(v_val_5698_);
                    crate::leanh::lean_dec_ref_known(v_subDir_x3f_5602_, 1);
                    v___x_5699_ = l_Lake_joinRelative(v_relGitDir_5695_, v_val_5698_);
                    v___y_5690_ = v___y_5697_;
                    v___y_5691_ = v___x_5699_;
                    state = 36;
                    continue;
                }
            }
            38 => {
                crate::leanh::lean_inc_ref(v_sname_5604_);
                v___x_5704_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_5437_, v_sname_5604_, v_gitDir_5700_, v___y_5703_, v___y_5702_);
                if crate::leanh::lean_obj_tag(v___x_5704_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5704_, 1);
                    v___y_5697_ = v_a_5437_;
                    state = 37;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_relGitDir_5695_);
                    crate::leanh::lean_dec_ref(v_sname_5604_);
                    crate::leanh::lean_dec(v_subDir_x3f_5602_);
                    crate::leanh::lean_dec_ref(v_url_5600_);
                    crate::leanh::lean_dec_ref(v_wsDir_5435_);
                    crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                    v_a_5705_ = crate::leanh::lean_ctor_get(v___x_5704_, 0);
                    v_isSharedCheck_5712_ = (!crate::leanh::lean_is_exclusive(v___x_5704_)) as u8;
                    if v_isSharedCheck_5712_ == 0 {
                        v___x_5707_ = v___x_5704_;
                        v_isShared_5708_ = v_isSharedCheck_5712_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5705_);
                        crate::leanh::lean_dec(v___x_5704_);
                        v___x_5707_ = crate::leanh::lean_box(0);
                        v_isShared_5708_ = v_isSharedCheck_5712_;
                        state = 39;
                        continue;
                    }
                }
            }
            39 => {
                if v_isShared_5708_ == 0 {
                    v___x_5710_ = v___x_5707_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5711_, 0, v_a_5705_);
                    v___x_5710_ = v_reuseFailAlloc_5711_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5710_;
            }
            41 => {
                v___x_5715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5715_, 0, v_rev_5601_);
                crate::leanh::lean_inc_ref(v_sname_5604_);
                v___x_5716_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_5437_, v_sname_5604_, v_gitDir_5700_, v___y_5714_, v___x_5715_);
                if crate::leanh::lean_obj_tag(v___x_5716_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5716_, 1);
                    v___y_5697_ = v_a_5437_;
                    state = 37;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_relGitDir_5695_);
                    crate::leanh::lean_dec_ref(v_sname_5604_);
                    crate::leanh::lean_dec(v_subDir_x3f_5602_);
                    crate::leanh::lean_dec_ref(v_url_5600_);
                    crate::leanh::lean_dec_ref(v_wsDir_5435_);
                    crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                    v_a_5717_ = crate::leanh::lean_ctor_get(v___x_5716_, 0);
                    v_isSharedCheck_5724_ = (!crate::leanh::lean_is_exclusive(v___x_5716_)) as u8;
                    if v_isSharedCheck_5724_ == 0 {
                        v___x_5719_ = v___x_5716_;
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5717_);
                        crate::leanh::lean_dec(v___x_5716_);
                        v___x_5719_ = crate::leanh::lean_box(0);
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 42;
                        continue;
                    }
                }
            }
            42 => {
                if v_isShared_5720_ == 0 {
                    v___x_5722_ = v___x_5719_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_5723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
                    v___x_5722_ = v_reuseFailAlloc_5723_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_5722_;
            }
            44 => {
                if v_a_5726_ == 0 {
                    crate::leanh::lean_dec_ref(v_gitDir_5700_);
                    v___y_5697_ = v_a_5437_;
                    state = 37;
                    continue;
                } else {
                    v___x_5727_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
                    crate::leanh::lean_inc_ref(v_sname_5604_);
                    v___x_5728_ = lean_string_append(v_sname_5604_, v___x_5727_);
                    v___x_5729_ = lean_string_append(v___x_5728_, v_gitDir_5700_);
                    crate::leanh::lean_dec_ref(v_gitDir_5700_);
                    v___x_5730_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
                    v___x_5731_ = lean_string_append(v___x_5729_, v___x_5730_);
                    v___x_5732_ = 2;
                    v___x_5733_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5733_, 0, v___x_5731_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5733_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_5732_,
                    );
                    crate::leanh::lean_inc_ref(v_a_5437_);
                    v___x_5734_ = crate::leanh::lean_apply_2(
                        v_a_5437_,
                        v___x_5733_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_5697_ = v_a_5437_;
                    state = 37;
                    continue;
                }
            }
            45 => {
                v___x_5739_ = lean_array_get_size(v___y_5737_);
                v___x_5740_ = lean_nat_dec_lt(v___y_5736_, v___x_5739_);
                if v___x_5740_ == 0 {
                    v_a_5726_ = v_val_5738_;
                    state = 44;
                    continue;
                } else {
                    v___x_5741_ = crate::leanh::lean_box(0);
                    v___x_5742_ = lean_nat_dec_le(v___x_5739_, v___x_5739_);
                    if v___x_5742_ == 0 {
                        if v___x_5740_ == 0 {
                            v_a_5726_ = v_val_5738_;
                            state = 44;
                            continue;
                        } else {
                            v___x_5743_ = 0usize;
                            v___x_5744_ = lean_usize_of_nat(v___x_5739_);
                            v___x_5745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_5737_, v___x_5743_, v___x_5744_, v___x_5741_, v_a_5437_);
                            if crate::leanh::lean_obj_tag(v___x_5745_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5745_, 1);
                                v_a_5726_ = v_val_5738_;
                                state = 44;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_gitDir_5700_);
                                crate::leanh::lean_dec_ref(v_relGitDir_5695_);
                                crate::leanh::lean_dec_ref(v_sname_5604_);
                                crate::leanh::lean_dec(v_subDir_x3f_5602_);
                                crate::leanh::lean_dec_ref(v_url_5600_);
                                crate::leanh::lean_dec_ref(v_wsDir_5435_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5746_ = crate::leanh::lean_ctor_get(v___x_5745_, 0);
                                v_isSharedCheck_5753_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5745_)) as u8;
                                if v_isSharedCheck_5753_ == 0 {
                                    v___x_5748_ = v___x_5745_;
                                    v_isShared_5749_ = v_isSharedCheck_5753_;
                                    state = 46;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5746_);
                                    crate::leanh::lean_dec(v___x_5745_);
                                    v___x_5748_ = crate::leanh::lean_box(0);
                                    v_isShared_5749_ = v_isSharedCheck_5753_;
                                    state = 46;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5754_ = 0usize;
                        v___x_5755_ = lean_usize_of_nat(v___x_5739_);
                        v___x_5756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_5737_, v___x_5754_, v___x_5755_, v___x_5741_, v_a_5437_);
                        if crate::leanh::lean_obj_tag(v___x_5756_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5756_, 1);
                            v_a_5726_ = v_val_5738_;
                            state = 44;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_gitDir_5700_);
                            crate::leanh::lean_dec_ref(v_relGitDir_5695_);
                            crate::leanh::lean_dec_ref(v_sname_5604_);
                            crate::leanh::lean_dec(v_subDir_x3f_5602_);
                            crate::leanh::lean_dec_ref(v_url_5600_);
                            crate::leanh::lean_dec_ref(v_wsDir_5435_);
                            crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5757_ = crate::leanh::lean_ctor_get(v___x_5756_, 0);
                            v_isSharedCheck_5764_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5756_)) as u8;
                            if v_isSharedCheck_5764_ == 0 {
                                v___x_5759_ = v___x_5756_;
                                v_isShared_5760_ = v_isSharedCheck_5764_;
                                state = 48;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5757_);
                                crate::leanh::lean_dec(v___x_5756_);
                                v___x_5759_ = crate::leanh::lean_box(0);
                                v_isShared_5760_ = v_isSharedCheck_5764_;
                                state = 48;
                                continue;
                            }
                        }
                    }
                }
            }
            46 => {
                if v_isShared_5749_ == 0 {
                    v___x_5751_ = v___x_5748_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_5752_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5746_);
                    v___x_5751_ = v_reuseFailAlloc_5752_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_5751_;
            }
            48 => {
                if v_isShared_5760_ == 0 {
                    v___x_5762_ = v___x_5759_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_5763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
                    v___x_5762_ = v_reuseFailAlloc_5763_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_5762_;
            }
            50 => {
                v___x_5768_ = crate::leanh::lean_alloc_closure(
                    l_instDecidableEqString___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                v___x_5769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5769_, 0, v_rev_5601_);
                crate::leanh::lean_inc_ref(v___x_5769_);
                v___x_5770_ =
                    l_Option_instDecidableEq___redArg(v___x_5768_, v_a_5767_, v___x_5769_);
                if v___x_5770_ == 0 {
                    v_pkgUrlMap_5771_ = crate::leanh::lean_ctor_get(v_lakeEnv_5434_, 5);
                    v___x_5772_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_5771_, v_name_5598_);
                    if crate::leanh::lean_obj_tag(v___x_5772_) == 0 {
                        crate::leanh::lean_inc_ref(v_url_5600_);
                        v___y_5702_ = v___x_5769_;
                        v___y_5703_ = v_url_5600_;
                        state = 38;
                        continue;
                    } else {
                        v_val_5773_ = crate::leanh::lean_ctor_get(v___x_5772_, 0);
                        crate::leanh::lean_inc(v_val_5773_);
                        crate::leanh::lean_dec_ref_known(v___x_5772_, 1);
                        v___y_5702_ = v___x_5769_;
                        v___y_5703_ = v_val_5773_;
                        state = 38;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5769_, 1);
                    crate::leanh::lean_inc_ref(v_gitDir_5700_);
                    v___x_5774_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_5700_);
                    v___x_5775_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5776_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    if v___x_5774_ == 0 {
                        v___y_5736_ = v___x_5775_;
                        v___y_5737_ = v___x_5776_;
                        v_val_5738_ = v___y_5766_;
                        state = 45;
                        continue;
                    } else {
                        v___y_5736_ = v___x_5775_;
                        v___y_5737_ = v___x_5776_;
                        v_val_5738_ = v___x_5603_;
                        state = 45;
                        continue;
                    }
                }
            }
            51 => {
                if v___x_5777_ == 0 {
                    v_pkgUrlMap_5779_ = crate::leanh::lean_ctor_get(v_lakeEnv_5434_, 5);
                    v___x_5780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_5779_, v_name_5598_);
                    if crate::leanh::lean_obj_tag(v___x_5780_) == 0 {
                        crate::leanh::lean_inc_ref(v_url_5600_);
                        v___y_5714_ = v_url_5600_;
                        state = 41;
                        continue;
                    } else {
                        v_val_5781_ = crate::leanh::lean_ctor_get(v___x_5780_, 0);
                        crate::leanh::lean_inc(v_val_5781_);
                        crate::leanh::lean_dec_ref_known(v___x_5780_, 1);
                        v___y_5714_ = v_val_5781_;
                        state = 41;
                        continue;
                    }
                } else {
                    v___x_5782_ = l_Lake_PackageEntry_materialize___closed__0;
                    crate::leanh::lean_inc_ref(v_gitDir_5700_);
                    v___x_5783_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_5782_, v_gitDir_5700_);
                    v___x_5784_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_5785_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
                    if v___x_5785_ == 0 {
                        v___y_5766_ = v___x_5777_;
                        v_a_5767_ = v___x_5783_;
                        state = 50;
                        continue;
                    } else {
                        v___x_5786_ = crate::leanh::lean_box(0);
                        v___x_5787_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                        if v___x_5787_ == 0 {
                            if v___x_5785_ == 0 {
                                v___y_5766_ = v___x_5777_;
                                v_a_5767_ = v___x_5783_;
                                state = 50;
                                continue;
                            } else {
                                v___x_5788_ = 0usize;
                                v___x_5789_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                v___x_5790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5784_, v___x_5788_, v___x_5789_, v___x_5786_, v_a_5437_);
                                if crate::leanh::lean_obj_tag(v___x_5790_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5790_, 1);
                                    v___y_5766_ = v___x_5777_;
                                    v_a_5767_ = v___x_5783_;
                                    state = 50;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_5783_);
                                    crate::leanh::lean_dec_ref(v_gitDir_5700_);
                                    crate::leanh::lean_dec_ref(v_relGitDir_5695_);
                                    crate::leanh::lean_dec_ref(v_sname_5604_);
                                    crate::leanh::lean_dec(v_subDir_x3f_5602_);
                                    crate::leanh::lean_dec_ref(v_rev_5601_);
                                    crate::leanh::lean_dec_ref(v_url_5600_);
                                    crate::leanh::lean_dec_ref(v_wsDir_5435_);
                                    crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                    v_a_5791_ = crate::leanh::lean_ctor_get(v___x_5790_, 0);
                                    v_isSharedCheck_5798_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5790_)) as u8;
                                    if v_isSharedCheck_5798_ == 0 {
                                        v___x_5793_ = v___x_5790_;
                                        v_isShared_5794_ = v_isSharedCheck_5798_;
                                        state = 52;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5791_);
                                        crate::leanh::lean_dec(v___x_5790_);
                                        v___x_5793_ = crate::leanh::lean_box(0);
                                        v_isShared_5794_ = v_isSharedCheck_5798_;
                                        state = 52;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_5799_ = 0usize;
                            v___x_5800_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_5801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5784_, v___x_5799_, v___x_5800_, v___x_5786_, v_a_5437_);
                            if crate::leanh::lean_obj_tag(v___x_5801_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5801_, 1);
                                v___y_5766_ = v___x_5777_;
                                v_a_5767_ = v___x_5783_;
                                state = 50;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5783_);
                                crate::leanh::lean_dec_ref(v_gitDir_5700_);
                                crate::leanh::lean_dec_ref(v_relGitDir_5695_);
                                crate::leanh::lean_dec_ref(v_sname_5604_);
                                crate::leanh::lean_dec(v_subDir_x3f_5602_);
                                crate::leanh::lean_dec_ref(v_rev_5601_);
                                crate::leanh::lean_dec_ref(v_url_5600_);
                                crate::leanh::lean_dec_ref(v_wsDir_5435_);
                                crate::leanh::lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5802_ = crate::leanh::lean_ctor_get(v___x_5801_, 0);
                                v_isSharedCheck_5809_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5801_)) as u8;
                                if v_isSharedCheck_5809_ == 0 {
                                    v___x_5804_ = v___x_5801_;
                                    v_isShared_5805_ = v_isSharedCheck_5809_;
                                    state = 54;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5802_);
                                    crate::leanh::lean_dec(v___x_5801_);
                                    v___x_5804_ = crate::leanh::lean_box(0);
                                    v_isShared_5805_ = v_isSharedCheck_5809_;
                                    state = 54;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            52 => {
                if v_isShared_5794_ == 0 {
                    v___x_5796_ = v___x_5793_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_5797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_a_5791_);
                    v___x_5796_ = v_reuseFailAlloc_5797_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_5796_;
            }
            54 => {
                if v_isShared_5805_ == 0 {
                    v___x_5807_ = v___x_5804_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_5808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5808_, 0, v_a_5802_);
                    v___x_5807_ = v_reuseFailAlloc_5808_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_5807_;
            }
            56 => {
                if v_isShared_5820_ == 0 {
                    v___x_5822_ = v___x_5819_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_5823_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_a_5817_);
                    v___x_5822_ = v_reuseFailAlloc_5823_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_5822_;
            }
            58 => {
                if v_isShared_5831_ == 0 {
                    v___x_5833_ = v___x_5830_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_5834_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5828_);
                    v___x_5833_ = v_reuseFailAlloc_5834_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_5833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PackageEntry_materialize___boxed(
    mut v_manifestEntry_5836_: *mut crate::leanh::LeanObject,
    mut v_lakeEnv_5837_: *mut crate::leanh::LeanObject,
    mut v_wsDir_5838_: *mut crate::leanh::LeanObject,
    mut v_relPkgsDir_5839_: *mut crate::leanh::LeanObject,
    mut v_a_5840_: *mut crate::leanh::LeanObject,
    mut v_a_5841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5842_ = l_Lake_PackageEntry_materialize(
        v_manifestEntry_5836_,
        v_lakeEnv_5837_,
        v_wsDir_5838_,
        v_relPkgsDir_5839_,
        v_a_5840_,
    );
    crate::leanh::lean_dec_ref(v_a_5840_);
    crate::leanh::lean_dec_ref(v_lakeEnv_5837_);
    return v_res_5842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Materialize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Env(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Manifest(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Reservoir(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instInhabitedMaterializedDep_default =
        _init_l_Lake_instInhabitedMaterializedDep_default();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default);
    l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Materialize(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Materialize(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Env(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Manifest(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Reservoir(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Materialize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Materialize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Load_Materialize(builtin);
}
