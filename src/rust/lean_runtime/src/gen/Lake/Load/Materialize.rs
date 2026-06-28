// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: Lake.Config.Env Lake.Load.Manifest Lake.Config.Package Lake.Util.Git Lake.Util.IO Lake.Reservoir
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_dec_eq, lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_realpath;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint8_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value:
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
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value:
    LeanStringObject<26> = LeanStringObject {
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
        58, 32, 99, 104, 101, 99, 107, 105, 110, 103, 32, 111, 117, 116, 32, 114, 101, 118, 105,
        115, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value:
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
    m_data: [58, 32, 99, 108, 111, 110, 105, 110, 103, 32, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0_value:
    LeanStringObject<30> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3_value:
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
    m_data: [39, 32, 109, 97, 110, 117, 97, 108, 108, 121, 0],
};
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3_value)
        as *mut LeanObject;
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5: u8 = 0;
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6: u8 = 0;
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7: usize = 0;
pub static l_Lake_instInhabitedMaterializedDep_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedMaterializedDep_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedMaterializedDep_default___closed__1_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116,
            96, 32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
        ],
    };
static mut l_Lake_instInhabitedMaterializedDep_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedMaterializedDep_default___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedMaterializedDep_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedMaterializedDep_default___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedMaterializedDep_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__3_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedMaterializedDep_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedMaterializedDep_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedMaterializedDep_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedMaterializedDep: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1_value:
    LeanStringObject<158> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3_value:
    LeanStringObject<71> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7_value:
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
        10, 32, 32, 32, 32, 118, 101, 114, 115, 105, 111, 110, 32, 61, 32, 0,
    ],
};
static mut l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7_value)
        as *mut LeanObject;
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58, 32, 0]};
static mut l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3_value
) as *mut LeanObject;
pub static l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [103, 105, 116, 35, 0]};
static mut l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__0_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__0_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__1_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__2_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__2_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__3_value: LeanStringObject<96> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__3_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__4_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__4_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__5_value: LeanStringObject<16> =
    LeanStringObject {
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
            96, 32, 97, 116, 32, 114, 101, 118, 105, 115, 105, 111, 110, 32, 96, 0,
        ],
    };
static mut l_Lake_Dependency_materialize___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__5_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__6_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__6_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__7_value: LeanStringObject<93> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__7_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__8_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__8_value) as *mut LeanObject;
pub static l_Lake_Dependency_materialize___closed__9_value: LeanStringObject<93> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Dependency_materialize___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dependency_materialize___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 11 }, m_objs: [core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake_instInhabitedMaterializedDep_default___closed__0_value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__0_value) as *mut LeanObject] };
static mut l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1_value
) as *mut LeanObject;
pub static l_Lake_PackageEntry_materialize___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_PackageEntry_materialize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_materialize___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(
    mut v_as_2922_: *mut LeanObject,
    mut v_i_2923_: usize,
    mut v_stop_2924_: usize,
    mut v_b_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2928_: u8 = 0;
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: usize = 0;
    let mut v___x_2932_: usize = 0;
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2928_ = lean_usize_dec_eq(v_i_2923_, v_stop_2924_);
                if v___x_2928_ == 0 {
                    v___x_2929_ = lean_array_uget_borrowed(v_as_2922_, v_i_2923_);
                    lean_inc_ref(v___y_2926_);
                    lean_inc(v___x_2929_);
                    v___x_2930_ = lean_apply_2(v___y_2926_, v___x_2929_, lean_box(0));
                    v___x_2931_ = 1usize;
                    v___x_2932_ = lean_usize_add(v_i_2923_, v___x_2931_);
                    v_i_2923_ = v___x_2932_;
                    v_b_2925_ = v___x_2930_;
                    state = 0;
                    continue;
                } else {
                    v___x_2934_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2934_, 0, v_b_2925_);
                    return v___x_2934_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0___boxed(
    mut v_as_2935_: *mut LeanObject,
    mut v_i_2936_: *mut LeanObject,
    mut v_stop_2937_: *mut LeanObject,
    mut v_b_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
    mut v___y_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2941_: usize = 0;
    let mut v_stop_boxed_2942_: usize = 0;
    let mut v_res_2943_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2941_ = lean_unbox_usize(v_i_2936_);
    lean_dec(v_i_2936_);
    v_stop_boxed_2942_ = lean_unbox_usize(v_stop_2937_);
    lean_dec(v_stop_2937_);
    v_res_2943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_as_2935_, v_i_boxed_2941_, v_stop_boxed_2942_, v_b_2938_, v___y_2939_);
    lean_dec_ref(v___y_2939_);
    lean_dec_ref(v_as_2935_);
    return v_res_2943_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(
    mut v_name_2950_: *mut LeanObject,
    mut v_repo_2951_: *mut LeanObject,
    mut v_rev_x3f_2952_: *mut LeanObject,
    mut v_a_2953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2956_: u8 = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2971_: u8 = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: u8 = 0;
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2976_: usize = 0;
    let mut v___x_2977_: usize = 0;
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: usize = 0;
    let mut v___x_2980_: usize = 0;
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: u8 = 0;
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: usize = 0;
    let mut v___x_3001_: usize = 0;
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3009_: u8 = 0;
    let mut v_unused_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: usize = 0;
    let mut v___x_3012_: usize = 0;
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v_unused_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: usize = 0;
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: usize = 0;
    let mut v___x_3033_: usize = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: u8 = 0;
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: u8 = 0;
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: u8 = 0;
    let mut v___x_3057_: usize = 0;
    let mut v___x_3058_: usize = 0;
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: usize = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: u8 = 0;
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: usize = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: usize = 0;
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: usize = 0;
    let mut v___x_3104_: usize = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: usize = 0;
    let mut v___x_3114_: usize = 0;
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: usize = 0;
    let mut v___x_3117_: usize = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: u8 = 0;
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: usize = 0;
    let mut v___x_3124_: usize = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: usize = 0;
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: usize = 0;
    let mut v___x_3137_: usize = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: usize = 0;
    let mut v___x_3140_: usize = 0;
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3086_ = l_Lake_Git_defaultRemote;
                v___x_3087_ = lean_unsigned_to_nat(0);
                v___x_3088_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                lean_inc_ref(v_repo_2951_);
                v___x_3089_ = l_Lake_GitRepo_findRemoteRevision(
                    v_repo_2951_,
                    v_rev_x3f_2952_,
                    v___x_3086_,
                    v___x_3088_,
                );
                if lean_obj_tag(v___x_3089_) == 0 {
                    v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
                    lean_inc(v_a_3090_);
                    v_a_3091_ = lean_ctor_get(v___x_3089_, 1);
                    lean_inc(v_a_3091_);
                    lean_dec_ref_known(v___x_3089_, 2);
                    v___x_3119_ = lean_array_get_size(v_a_3091_);
                    v___x_3120_ = lean_nat_dec_lt(v___x_3087_, v___x_3119_);
                    if v___x_3120_ == 0 {
                        lean_dec(v_a_3091_);
                        state = 14;
                        continue;
                    } else {
                        v___x_3121_ = lean_box(0);
                        v___x_3122_ = lean_nat_dec_le(v___x_3119_, v___x_3119_);
                        if v___x_3122_ == 0 {
                            if v___x_3120_ == 0 {
                                lean_dec(v_a_3091_);
                                state = 14;
                                continue;
                            } else {
                                v___x_3123_ = 0usize;
                                v___x_3124_ = lean_usize_of_nat(v___x_3119_);
                                v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3091_, v___x_3123_, v___x_3124_, v___x_3121_, v_a_2953_);
                                lean_dec(v_a_3091_);
                                if lean_obj_tag(v___x_3125_) == 0 {
                                    lean_dec_ref_known(v___x_3125_, 1);
                                    state = 14;
                                    continue;
                                } else {
                                    lean_dec(v_a_3090_);
                                    lean_dec_ref(v_repo_2951_);
                                    lean_dec_ref(v_name_2950_);
                                    return v___x_3125_;
                                }
                            }
                        } else {
                            v___x_3126_ = 0usize;
                            v___x_3127_ = lean_usize_of_nat(v___x_3119_);
                            v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3091_, v___x_3126_, v___x_3127_, v___x_3121_, v_a_2953_);
                            lean_dec(v_a_3091_);
                            if lean_obj_tag(v___x_3128_) == 0 {
                                lean_dec_ref_known(v___x_3128_, 1);
                                state = 14;
                                continue;
                            } else {
                                lean_dec(v_a_3090_);
                                lean_dec_ref(v_repo_2951_);
                                lean_dec_ref(v_name_2950_);
                                return v___x_3128_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_repo_2951_);
                    lean_dec_ref(v_name_2950_);
                    v_a_3129_ = lean_ctor_get(v___x_3089_, 1);
                    lean_inc(v_a_3129_);
                    lean_dec_ref_known(v___x_3089_, 2);
                    v___x_3130_ = lean_array_get_size(v_a_3129_);
                    v___x_3131_ = lean_nat_dec_lt(v___x_3087_, v___x_3130_);
                    if v___x_3131_ == 0 {
                        lean_dec(v_a_3129_);
                        v___x_3132_ = lean_box(0);
                        v___x_3133_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3133_, 0, v___x_3132_);
                        return v___x_3133_;
                    } else {
                        v___x_3134_ = lean_box(0);
                        v___x_3135_ = lean_nat_dec_le(v___x_3130_, v___x_3130_);
                        if v___x_3135_ == 0 {
                            if v___x_3131_ == 0 {
                                lean_dec(v_a_3129_);
                                state = 13;
                                continue;
                            } else {
                                v___x_3136_ = 0usize;
                                v___x_3137_ = lean_usize_of_nat(v___x_3130_);
                                v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3129_, v___x_3136_, v___x_3137_, v___x_3134_, v_a_2953_);
                                lean_dec(v_a_3129_);
                                if lean_obj_tag(v___x_3138_) == 0 {
                                    lean_dec_ref_known(v___x_3138_, 1);
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
                            lean_dec(v_a_3129_);
                            if lean_obj_tag(v___x_3141_) == 0 {
                                lean_dec_ref_known(v___x_3141_, 1);
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
                    lean_dec_ref(v_repo_2951_);
                    lean_dec_ref(v_name_2950_);
                    v___x_2957_ = lean_box(0);
                    v___x_2958_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2958_, 0, v___x_2957_);
                    return v___x_2958_;
                } else {
                    v___x_2959_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
                    v___x_2960_ = lean_string_append(v_name_2950_, v___x_2959_);
                    v___x_2961_ = lean_string_append(v___x_2960_, v_repo_2951_);
                    lean_dec_ref(v_repo_2951_);
                    v___x_2962_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
                    v___x_2963_ = lean_string_append(v___x_2961_, v___x_2962_);
                    v___x_2964_ = 2;
                    v___x_2965_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2965_, 0, v___x_2963_);
                    lean_ctor_set_uint8(
                        v___x_2965_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2964_,
                    );
                    lean_inc_ref(v_a_2953_);
                    v___x_2966_ = lean_apply_2(v_a_2953_, v___x_2965_, lean_box(0));
                    v___x_2967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2967_, 0, v___x_2966_);
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
                    v___x_2974_ = lean_box(0);
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
                            if lean_obj_tag(v___x_2978_) == 0 {
                                lean_dec_ref_known(v___x_2978_, 1);
                                v_a_2956_ = v_val_2971_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_repo_2951_);
                                lean_dec_ref(v_name_2950_);
                                return v___x_2978_;
                            }
                        }
                    } else {
                        v___x_2979_ = 0usize;
                        v___x_2980_ = lean_usize_of_nat(v___x_2972_);
                        v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_2970_, v___x_2979_, v___x_2980_, v___x_2974_, v_a_2953_);
                        if lean_obj_tag(v___x_2981_) == 0 {
                            lean_dec_ref_known(v___x_2981_, 1);
                            v_a_2956_ = v_val_2971_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_repo_2951_);
                            lean_dec_ref(v_name_2950_);
                            return v___x_2981_;
                        }
                    }
                }
            }
            3 => {
                v___x_2983_ = lean_box(0);
                v___x_2984_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2984_, 0, v___x_2983_);
                return v___x_2984_;
            }
            4 => {
                v___x_2986_ = lean_box(0);
                v___x_2987_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2987_, 0, v___x_2986_);
                return v___x_2987_;
            }
            5 => {
                v___x_2989_ = lean_unsigned_to_nat(0);
                v___x_2990_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_2991_ = l_Lake_GitRepo_clean(v_repo_2951_, v___x_2990_);
                if lean_obj_tag(v___x_2991_) == 0 {
                    v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
                    lean_inc(v_a_2992_);
                    v_a_2993_ = lean_ctor_get(v___x_2991_, 1);
                    lean_inc(v_a_2993_);
                    lean_dec_ref_known(v___x_2991_, 2);
                    v___x_2994_ = lean_array_get_size(v_a_2993_);
                    v___x_2995_ = lean_nat_dec_lt(v___x_2989_, v___x_2994_);
                    if v___x_2995_ == 0 {
                        lean_dec(v_a_2993_);
                        v___x_2996_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2996_, 0, v_a_2992_);
                        return v___x_2996_;
                    } else {
                        v___x_2997_ = lean_box(0);
                        v___x_2998_ = lean_nat_dec_le(v___x_2994_, v___x_2994_);
                        if v___x_2998_ == 0 {
                            if v___x_2995_ == 0 {
                                lean_dec(v_a_2993_);
                                v___x_2999_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2999_, 0, v_a_2992_);
                                return v___x_2999_;
                            } else {
                                v___x_3000_ = 0usize;
                                v___x_3001_ = lean_usize_of_nat(v___x_2994_);
                                v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2993_, v___x_3000_, v___x_3001_, v___x_2997_, v_a_2953_);
                                lean_dec(v_a_2993_);
                                if lean_obj_tag(v___x_3002_) == 0 {
                                    v_isSharedCheck_3009_ = (!lean_is_exclusive(v___x_3002_)) as u8;
                                    if v_isSharedCheck_3009_ == 0 {
                                        v_unused_3010_ = lean_ctor_get(v___x_3002_, 0);
                                        lean_dec(v_unused_3010_);
                                        v___x_3004_ = v___x_3002_;
                                        v_isShared_3005_ = v_isSharedCheck_3009_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3002_);
                                        v___x_3004_ = lean_box(0);
                                        v_isShared_3005_ = v_isSharedCheck_3009_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_2992_);
                                    return v___x_3002_;
                                }
                            }
                        } else {
                            v___x_3011_ = 0usize;
                            v___x_3012_ = lean_usize_of_nat(v___x_2994_);
                            v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_2993_, v___x_3011_, v___x_3012_, v___x_2997_, v_a_2953_);
                            lean_dec(v_a_2993_);
                            if lean_obj_tag(v___x_3013_) == 0 {
                                v_isSharedCheck_3020_ = (!lean_is_exclusive(v___x_3013_)) as u8;
                                if v_isSharedCheck_3020_ == 0 {
                                    v_unused_3021_ = lean_ctor_get(v___x_3013_, 0);
                                    lean_dec(v_unused_3021_);
                                    v___x_3015_ = v___x_3013_;
                                    v_isShared_3016_ = v_isSharedCheck_3020_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_dec(v___x_3013_);
                                    v___x_3015_ = lean_box(0);
                                    v_isShared_3016_ = v_isSharedCheck_3020_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_2992_);
                                return v___x_3013_;
                            }
                        }
                    }
                } else {
                    v_a_3022_ = lean_ctor_get(v___x_2991_, 1);
                    lean_inc(v_a_3022_);
                    lean_dec_ref_known(v___x_2991_, 2);
                    v___x_3023_ = lean_array_get_size(v_a_3022_);
                    v___x_3024_ = lean_nat_dec_lt(v___x_2989_, v___x_3023_);
                    if v___x_3024_ == 0 {
                        lean_dec(v_a_3022_);
                        v___x_3025_ = lean_box(0);
                        v___x_3026_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3026_, 0, v___x_3025_);
                        return v___x_3026_;
                    } else {
                        v___x_3027_ = lean_box(0);
                        v___x_3028_ = lean_nat_dec_le(v___x_3023_, v___x_3023_);
                        if v___x_3028_ == 0 {
                            if v___x_3024_ == 0 {
                                lean_dec(v_a_3022_);
                                state = 4;
                                continue;
                            } else {
                                v___x_3029_ = 0usize;
                                v___x_3030_ = lean_usize_of_nat(v___x_3023_);
                                v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3022_, v___x_3029_, v___x_3030_, v___x_3027_, v_a_2953_);
                                lean_dec(v_a_3022_);
                                if lean_obj_tag(v___x_3031_) == 0 {
                                    lean_dec_ref_known(v___x_3031_, 1);
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
                            lean_dec(v_a_3022_);
                            if lean_obj_tag(v___x_3034_) == 0 {
                                lean_dec_ref_known(v___x_3034_, 1);
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
                    lean_ctor_set(v___x_3004_, 0, v_a_2992_);
                    v___x_3007_ = v___x_3004_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_2992_);
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
                    lean_ctor_set(v___x_3015_, 0, v_a_2992_);
                    v___x_3018_ = v___x_3015_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_2992_);
                    v___x_3018_ = v_reuseFailAlloc_3019_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3018_;
            }
            10 => {
                if lean_obj_tag(v___y_3036_) == 0 {
                    lean_dec_ref_known(v___y_3036_, 1);
                    state = 5;
                    continue;
                } else {
                    lean_dec_ref(v_repo_2951_);
                    return v___y_3036_;
                }
            }
            11 => {
                v___x_3040_ = lean_string_dec_eq(v_a_3039_, v___y_3038_);
                lean_dec_ref(v_a_3039_);
                if v___x_3040_ == 0 {
                    v___x_3041_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
                    v___x_3042_ = lean_string_append(v_name_2950_, v___x_3041_);
                    v___x_3043_ = lean_string_append(v___x_3042_, v___y_3038_);
                    v___x_3044_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
                    v___x_3045_ = lean_string_append(v___x_3043_, v___x_3044_);
                    v___x_3046_ = 1;
                    v___x_3047_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3047_, 0, v___x_3045_);
                    lean_ctor_set_uint8(
                        v___x_3047_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_3046_,
                    );
                    lean_inc_ref(v_a_2953_);
                    v___x_3048_ = lean_apply_2(v_a_2953_, v___x_3047_, lean_box(0));
                    v___x_3049_ = lean_unsigned_to_nat(0);
                    v___x_3050_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    lean_inc_ref(v_repo_2951_);
                    v___x_3051_ =
                        l_Lake_GitRepo_checkoutDetach(v___y_3038_, v_repo_2951_, v___x_3050_);
                    if lean_obj_tag(v___x_3051_) == 0 {
                        v_a_3052_ = lean_ctor_get(v___x_3051_, 1);
                        lean_inc(v_a_3052_);
                        lean_dec_ref_known(v___x_3051_, 2);
                        v___x_3053_ = lean_array_get_size(v_a_3052_);
                        v___x_3054_ = lean_nat_dec_lt(v___x_3049_, v___x_3053_);
                        if v___x_3054_ == 0 {
                            lean_dec(v_a_3052_);
                            state = 5;
                            continue;
                        } else {
                            v___x_3055_ = lean_box(0);
                            v___x_3056_ = lean_nat_dec_le(v___x_3053_, v___x_3053_);
                            if v___x_3056_ == 0 {
                                if v___x_3054_ == 0 {
                                    lean_dec(v_a_3052_);
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_3057_ = 0usize;
                                    v___x_3058_ = lean_usize_of_nat(v___x_3053_);
                                    v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3052_, v___x_3057_, v___x_3058_, v___x_3055_, v_a_2953_);
                                    lean_dec(v_a_3052_);
                                    if lean_obj_tag(v___x_3059_) == 0 {
                                        lean_dec_ref_known(v___x_3059_, 1);
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
                                lean_dec(v_a_3052_);
                                if lean_obj_tag(v___x_3062_) == 0 {
                                    lean_dec_ref_known(v___x_3062_, 1);
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
                        v_a_3063_ = lean_ctor_get(v___x_3051_, 1);
                        lean_inc(v_a_3063_);
                        lean_dec_ref_known(v___x_3051_, 2);
                        v___x_3064_ = lean_array_get_size(v_a_3063_);
                        v___x_3065_ = lean_nat_dec_lt(v___x_3049_, v___x_3064_);
                        if v___x_3065_ == 0 {
                            lean_dec(v_a_3063_);
                            lean_dec_ref(v_repo_2951_);
                            v___x_3066_ = lean_box(0);
                            v___x_3067_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3067_, 0, v___x_3066_);
                            return v___x_3067_;
                        } else {
                            v___x_3068_ = lean_box(0);
                            v___x_3069_ = lean_nat_dec_le(v___x_3064_, v___x_3064_);
                            if v___x_3069_ == 0 {
                                if v___x_3065_ == 0 {
                                    lean_dec(v_a_3063_);
                                    lean_dec_ref(v_repo_2951_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3070_ = 0usize;
                                    v___x_3071_ = lean_usize_of_nat(v___x_3064_);
                                    v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3063_, v___x_3070_, v___x_3071_, v___x_3068_, v_a_2953_);
                                    lean_dec(v_a_3063_);
                                    if lean_obj_tag(v___x_3072_) == 0 {
                                        lean_dec_ref_known(v___x_3072_, 1);
                                        lean_dec_ref(v_repo_2951_);
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
                                lean_dec(v_a_3063_);
                                if lean_obj_tag(v___x_3075_) == 0 {
                                    lean_dec_ref_known(v___x_3075_, 1);
                                    lean_dec_ref(v_repo_2951_);
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
                    lean_dec_ref(v___y_3038_);
                    lean_inc_ref(v_repo_2951_);
                    v___x_3076_ = l_Lake_GitRepo_hasNoDiff(v_repo_2951_);
                    v___x_3077_ = lean_unsigned_to_nat(0);
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
                v___x_3081_ = lean_box(0);
                v___x_3082_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3082_, 0, v___x_3081_);
                return v___x_3082_;
            }
            13 => {
                v___x_3084_ = lean_box(0);
                v___x_3085_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3085_, 0, v___x_3084_);
                return v___x_3085_;
            }
            14 => {
                lean_inc_ref(v_repo_2951_);
                v___x_3093_ = l_Lake_GitRepo_getHeadRevision(v_repo_2951_, v___x_3088_);
                if lean_obj_tag(v___x_3093_) == 0 {
                    v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
                    lean_inc(v_a_3094_);
                    v_a_3095_ = lean_ctor_get(v___x_3093_, 1);
                    lean_inc(v_a_3095_);
                    lean_dec_ref_known(v___x_3093_, 2);
                    v___x_3096_ = lean_array_get_size(v_a_3095_);
                    v___x_3097_ = lean_nat_dec_lt(v___x_3087_, v___x_3096_);
                    if v___x_3097_ == 0 {
                        lean_dec(v_a_3095_);
                        v___y_3038_ = v_a_3090_;
                        v_a_3039_ = v_a_3094_;
                        state = 11;
                        continue;
                    } else {
                        v___x_3098_ = lean_box(0);
                        v___x_3099_ = lean_nat_dec_le(v___x_3096_, v___x_3096_);
                        if v___x_3099_ == 0 {
                            if v___x_3097_ == 0 {
                                lean_dec(v_a_3095_);
                                v___y_3038_ = v_a_3090_;
                                v_a_3039_ = v_a_3094_;
                                state = 11;
                                continue;
                            } else {
                                v___x_3100_ = 0usize;
                                v___x_3101_ = lean_usize_of_nat(v___x_3096_);
                                v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3095_, v___x_3100_, v___x_3101_, v___x_3098_, v_a_2953_);
                                lean_dec(v_a_3095_);
                                if lean_obj_tag(v___x_3102_) == 0 {
                                    lean_dec_ref_known(v___x_3102_, 1);
                                    v___y_3038_ = v_a_3090_;
                                    v_a_3039_ = v_a_3094_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_dec(v_a_3094_);
                                    lean_dec(v_a_3090_);
                                    lean_dec_ref(v_repo_2951_);
                                    lean_dec_ref(v_name_2950_);
                                    return v___x_3102_;
                                }
                            }
                        } else {
                            v___x_3103_ = 0usize;
                            v___x_3104_ = lean_usize_of_nat(v___x_3096_);
                            v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3095_, v___x_3103_, v___x_3104_, v___x_3098_, v_a_2953_);
                            lean_dec(v_a_3095_);
                            if lean_obj_tag(v___x_3105_) == 0 {
                                lean_dec_ref_known(v___x_3105_, 1);
                                v___y_3038_ = v_a_3090_;
                                v_a_3039_ = v_a_3094_;
                                state = 11;
                                continue;
                            } else {
                                lean_dec(v_a_3094_);
                                lean_dec(v_a_3090_);
                                lean_dec_ref(v_repo_2951_);
                                lean_dec_ref(v_name_2950_);
                                return v___x_3105_;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_3090_);
                    lean_dec_ref(v_repo_2951_);
                    lean_dec_ref(v_name_2950_);
                    v_a_3106_ = lean_ctor_get(v___x_3093_, 1);
                    lean_inc(v_a_3106_);
                    lean_dec_ref_known(v___x_3093_, 2);
                    v___x_3107_ = lean_array_get_size(v_a_3106_);
                    v___x_3108_ = lean_nat_dec_lt(v___x_3087_, v___x_3107_);
                    if v___x_3108_ == 0 {
                        lean_dec(v_a_3106_);
                        v___x_3109_ = lean_box(0);
                        v___x_3110_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3110_, 0, v___x_3109_);
                        return v___x_3110_;
                    } else {
                        v___x_3111_ = lean_box(0);
                        v___x_3112_ = lean_nat_dec_le(v___x_3107_, v___x_3107_);
                        if v___x_3112_ == 0 {
                            if v___x_3108_ == 0 {
                                lean_dec(v_a_3106_);
                                state = 12;
                                continue;
                            } else {
                                v___x_3113_ = 0usize;
                                v___x_3114_ = lean_usize_of_nat(v___x_3107_);
                                v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3106_, v___x_3113_, v___x_3114_, v___x_3111_, v_a_2953_);
                                lean_dec(v_a_3106_);
                                if lean_obj_tag(v___x_3115_) == 0 {
                                    lean_dec_ref_known(v___x_3115_, 1);
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
                            lean_dec(v_a_3106_);
                            if lean_obj_tag(v___x_3118_) == 0 {
                                lean_dec_ref_known(v___x_3118_, 1);
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
    mut v_name_3142_: *mut LeanObject,
    mut v_repo_3143_: *mut LeanObject,
    mut v_rev_x3f_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3147_: *mut LeanObject = core::ptr::null_mut();
    v_res_3147_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg(
        v_name_3142_,
        v_repo_3143_,
        v_rev_x3f_3144_,
        v_a_3145_,
    );
    lean_dec_ref(v_a_3145_);
    return v_res_3147_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(
    mut v_name_3149_: *mut LeanObject,
    mut v_repo_3150_: *mut LeanObject,
    mut v_url_3151_: *mut LeanObject,
    mut v_rev_x3f_3152_: *mut LeanObject,
    mut v_a_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: usize = 0;
    let mut v___x_3180_: usize = 0;
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3184_: u8 = 0;
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v_unused_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: usize = 0;
    let mut v___x_3191_: usize = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_unused_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: usize = 0;
    let mut v___x_3209_: usize = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: usize = 0;
    let mut v___x_3212_: usize = 0;
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: usize = 0;
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: u8 = 0;
    let mut v___x_3247_: usize = 0;
    let mut v___x_3248_: usize = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: u8 = 0;
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: u8 = 0;
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: usize = 0;
    let mut v___x_3279_: usize = 0;
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: u8 = 0;
    let mut v___x_3288_: usize = 0;
    let mut v___x_3289_: usize = 0;
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: usize = 0;
    let mut v___x_3292_: usize = 0;
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3261_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
                lean_inc_ref(v_name_3149_);
                v___x_3262_ = lean_string_append(v_name_3149_, v___x_3261_);
                v___x_3263_ = lean_string_append(v___x_3262_, v_url_3151_);
                v___x_3264_ = 1;
                v___x_3265_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_3265_, 0, v___x_3263_);
                lean_ctor_set_uint8(
                    v___x_3265_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3264_,
                );
                lean_inc_ref(v_a_3153_);
                v___x_3266_ = lean_apply_2(v_a_3153_, v___x_3265_, lean_box(0));
                v___x_3267_ = lean_unsigned_to_nat(0);
                v___x_3268_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                lean_inc_ref(v_repo_3150_);
                v___x_3269_ = l_Lake_GitRepo_clone(v_url_3151_, v_repo_3150_, v___x_3268_);
                if lean_obj_tag(v___x_3269_) == 0 {
                    v_a_3270_ = lean_ctor_get(v___x_3269_, 1);
                    lean_inc(v_a_3270_);
                    lean_dec_ref_known(v___x_3269_, 2);
                    v___x_3271_ = lean_array_get_size(v_a_3270_);
                    v___x_3272_ = lean_nat_dec_lt(v___x_3267_, v___x_3271_);
                    if v___x_3272_ == 0 {
                        lean_dec(v_a_3270_);
                        state = 8;
                        continue;
                    } else {
                        v___x_3273_ = lean_box(0);
                        v___x_3274_ = lean_nat_dec_le(v___x_3271_, v___x_3271_);
                        if v___x_3274_ == 0 {
                            if v___x_3272_ == 0 {
                                lean_dec(v_a_3270_);
                                state = 8;
                                continue;
                            } else {
                                v___x_3275_ = 0usize;
                                v___x_3276_ = lean_usize_of_nat(v___x_3271_);
                                v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3270_, v___x_3275_, v___x_3276_, v___x_3273_, v_a_3153_);
                                lean_dec(v_a_3270_);
                                if lean_obj_tag(v___x_3277_) == 0 {
                                    lean_dec_ref_known(v___x_3277_, 1);
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
                            lean_dec(v_a_3270_);
                            if lean_obj_tag(v___x_3280_) == 0 {
                                lean_dec_ref_known(v___x_3280_, 1);
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
                    v_a_3281_ = lean_ctor_get(v___x_3269_, 1);
                    lean_inc(v_a_3281_);
                    lean_dec_ref_known(v___x_3269_, 2);
                    v___x_3282_ = lean_array_get_size(v_a_3281_);
                    v___x_3283_ = lean_nat_dec_lt(v___x_3267_, v___x_3282_);
                    if v___x_3283_ == 0 {
                        lean_dec(v_a_3281_);
                        lean_dec(v_rev_x3f_3152_);
                        lean_dec_ref(v_repo_3150_);
                        lean_dec_ref(v_name_3149_);
                        v___x_3284_ = lean_box(0);
                        v___x_3285_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3285_, 0, v___x_3284_);
                        return v___x_3285_;
                    } else {
                        v___x_3286_ = lean_box(0);
                        v___x_3287_ = lean_nat_dec_le(v___x_3282_, v___x_3282_);
                        if v___x_3287_ == 0 {
                            if v___x_3283_ == 0 {
                                lean_dec(v_a_3281_);
                                lean_dec(v_rev_x3f_3152_);
                                lean_dec_ref(v_repo_3150_);
                                lean_dec_ref(v_name_3149_);
                                state = 12;
                                continue;
                            } else {
                                v___x_3288_ = 0usize;
                                v___x_3289_ = lean_usize_of_nat(v___x_3282_);
                                v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3281_, v___x_3288_, v___x_3289_, v___x_3286_, v_a_3153_);
                                lean_dec(v_a_3281_);
                                if lean_obj_tag(v___x_3290_) == 0 {
                                    lean_dec_ref_known(v___x_3290_, 1);
                                    lean_dec(v_rev_x3f_3152_);
                                    lean_dec_ref(v_repo_3150_);
                                    lean_dec_ref(v_name_3149_);
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
                            lean_dec(v_a_3281_);
                            if lean_obj_tag(v___x_3293_) == 0 {
                                lean_dec_ref_known(v___x_3293_, 1);
                                lean_dec(v_rev_x3f_3152_);
                                lean_dec_ref(v_repo_3150_);
                                lean_dec_ref(v_name_3149_);
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
                v___x_3156_ = lean_box(0);
                v___x_3157_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3157_, 0, v___x_3156_);
                return v___x_3157_;
            }
            2 => {
                v___x_3160_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
                v___x_3161_ = lean_string_append(v_name_3149_, v___x_3160_);
                v___x_3162_ = lean_string_append(v___x_3161_, v_a_3159_);
                v___x_3163_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
                v___x_3164_ = lean_string_append(v___x_3162_, v___x_3163_);
                v___x_3165_ = 1;
                v___x_3166_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_3166_, 0, v___x_3164_);
                lean_ctor_set_uint8(
                    v___x_3166_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3165_,
                );
                lean_inc_ref(v_a_3153_);
                v___x_3167_ = lean_apply_2(v_a_3153_, v___x_3166_, lean_box(0));
                v___x_3168_ = lean_unsigned_to_nat(0);
                v___x_3169_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_3170_ = l_Lake_GitRepo_checkoutDetach(v_a_3159_, v_repo_3150_, v___x_3169_);
                if lean_obj_tag(v___x_3170_) == 0 {
                    v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
                    lean_inc(v_a_3171_);
                    v_a_3172_ = lean_ctor_get(v___x_3170_, 1);
                    lean_inc(v_a_3172_);
                    lean_dec_ref_known(v___x_3170_, 2);
                    v___x_3173_ = lean_array_get_size(v_a_3172_);
                    v___x_3174_ = lean_nat_dec_lt(v___x_3168_, v___x_3173_);
                    if v___x_3174_ == 0 {
                        lean_dec(v_a_3172_);
                        v___x_3175_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3175_, 0, v_a_3171_);
                        return v___x_3175_;
                    } else {
                        v___x_3176_ = lean_box(0);
                        v___x_3177_ = lean_nat_dec_le(v___x_3173_, v___x_3173_);
                        if v___x_3177_ == 0 {
                            if v___x_3174_ == 0 {
                                lean_dec(v_a_3172_);
                                v___x_3178_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3178_, 0, v_a_3171_);
                                return v___x_3178_;
                            } else {
                                v___x_3179_ = 0usize;
                                v___x_3180_ = lean_usize_of_nat(v___x_3173_);
                                v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3172_, v___x_3179_, v___x_3180_, v___x_3176_, v_a_3153_);
                                lean_dec(v_a_3172_);
                                if lean_obj_tag(v___x_3181_) == 0 {
                                    v_isSharedCheck_3188_ = (!lean_is_exclusive(v___x_3181_)) as u8;
                                    if v_isSharedCheck_3188_ == 0 {
                                        v_unused_3189_ = lean_ctor_get(v___x_3181_, 0);
                                        lean_dec(v_unused_3189_);
                                        v___x_3183_ = v___x_3181_;
                                        v_isShared_3184_ = v_isSharedCheck_3188_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3181_);
                                        v___x_3183_ = lean_box(0);
                                        v_isShared_3184_ = v_isSharedCheck_3188_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3171_);
                                    return v___x_3181_;
                                }
                            }
                        } else {
                            v___x_3190_ = 0usize;
                            v___x_3191_ = lean_usize_of_nat(v___x_3173_);
                            v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3172_, v___x_3190_, v___x_3191_, v___x_3176_, v_a_3153_);
                            lean_dec(v_a_3172_);
                            if lean_obj_tag(v___x_3192_) == 0 {
                                v_isSharedCheck_3199_ = (!lean_is_exclusive(v___x_3192_)) as u8;
                                if v_isSharedCheck_3199_ == 0 {
                                    v_unused_3200_ = lean_ctor_get(v___x_3192_, 0);
                                    lean_dec(v_unused_3200_);
                                    v___x_3194_ = v___x_3192_;
                                    v_isShared_3195_ = v_isSharedCheck_3199_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v___x_3192_);
                                    v___x_3194_ = lean_box(0);
                                    v_isShared_3195_ = v_isSharedCheck_3199_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3171_);
                                return v___x_3192_;
                            }
                        }
                    }
                } else {
                    v_a_3201_ = lean_ctor_get(v___x_3170_, 1);
                    lean_inc(v_a_3201_);
                    lean_dec_ref_known(v___x_3170_, 2);
                    v___x_3202_ = lean_array_get_size(v_a_3201_);
                    v___x_3203_ = lean_nat_dec_lt(v___x_3168_, v___x_3202_);
                    if v___x_3203_ == 0 {
                        lean_dec(v_a_3201_);
                        v___x_3204_ = lean_box(0);
                        v___x_3205_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3205_, 0, v___x_3204_);
                        return v___x_3205_;
                    } else {
                        v___x_3206_ = lean_box(0);
                        v___x_3207_ = lean_nat_dec_le(v___x_3202_, v___x_3202_);
                        if v___x_3207_ == 0 {
                            if v___x_3203_ == 0 {
                                lean_dec(v_a_3201_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3208_ = 0usize;
                                v___x_3209_ = lean_usize_of_nat(v___x_3202_);
                                v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3201_, v___x_3208_, v___x_3209_, v___x_3206_, v_a_3153_);
                                lean_dec(v_a_3201_);
                                if lean_obj_tag(v___x_3210_) == 0 {
                                    lean_dec_ref_known(v___x_3210_, 1);
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
                            lean_dec(v_a_3201_);
                            if lean_obj_tag(v___x_3213_) == 0 {
                                lean_dec_ref_known(v___x_3213_, 1);
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
                    lean_ctor_set(v___x_3183_, 0, v_a_3171_);
                    v___x_3186_ = v___x_3183_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3171_);
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
                    lean_ctor_set(v___x_3194_, 0, v_a_3171_);
                    v___x_3197_ = v___x_3194_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3171_);
                    v___x_3197_ = v_reuseFailAlloc_3198_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3197_;
            }
            7 => {
                v___x_3215_ = lean_box(0);
                v___x_3216_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3216_, 0, v___x_3215_);
                return v___x_3216_;
            }
            8 => {
                if lean_obj_tag(v_rev_x3f_3152_) == 1 {
                    v_val_3218_ = lean_ctor_get(v_rev_x3f_3152_, 0);
                    v_isSharedCheck_3253_ = (!lean_is_exclusive(v_rev_x3f_3152_)) as u8;
                    if v_isSharedCheck_3253_ == 0 {
                        v___x_3220_ = v_rev_x3f_3152_;
                        v_isShared_3221_ = v_isSharedCheck_3253_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_val_3218_);
                        lean_dec(v_rev_x3f_3152_);
                        v___x_3220_ = lean_box(0);
                        v_isShared_3221_ = v_isSharedCheck_3253_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_rev_x3f_3152_);
                    lean_dec_ref(v_repo_3150_);
                    lean_dec_ref(v_name_3149_);
                    v___x_3254_ = lean_box(0);
                    v___x_3255_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3255_, 0, v___x_3254_);
                    return v___x_3255_;
                }
            }
            9 => {
                v___x_3222_ = l_Lake_Git_defaultRemote;
                v___x_3223_ = lean_unsigned_to_nat(0);
                v___x_3224_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                lean_inc_ref(v_repo_3150_);
                v___x_3225_ = l_Lake_GitRepo_resolveRemoteRevision(
                    v_val_3218_,
                    v___x_3222_,
                    v_repo_3150_,
                    v___x_3224_,
                );
                if lean_obj_tag(v___x_3225_) == 0 {
                    lean_del_object(v___x_3220_);
                    v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
                    lean_inc(v_a_3226_);
                    v_a_3227_ = lean_ctor_get(v___x_3225_, 1);
                    lean_inc(v_a_3227_);
                    lean_dec_ref_known(v___x_3225_, 2);
                    v___x_3228_ = lean_array_get_size(v_a_3227_);
                    v___x_3229_ = lean_nat_dec_lt(v___x_3223_, v___x_3228_);
                    if v___x_3229_ == 0 {
                        lean_dec(v_a_3227_);
                        v_a_3159_ = v_a_3226_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3230_ = lean_box(0);
                        v___x_3231_ = lean_nat_dec_le(v___x_3228_, v___x_3228_);
                        if v___x_3231_ == 0 {
                            if v___x_3229_ == 0 {
                                lean_dec(v_a_3227_);
                                v_a_3159_ = v_a_3226_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3232_ = 0usize;
                                v___x_3233_ = lean_usize_of_nat(v___x_3228_);
                                v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3227_, v___x_3232_, v___x_3233_, v___x_3230_, v_a_3153_);
                                lean_dec(v_a_3227_);
                                if lean_obj_tag(v___x_3234_) == 0 {
                                    lean_dec_ref_known(v___x_3234_, 1);
                                    v_a_3159_ = v_a_3226_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v_a_3226_);
                                    lean_dec_ref(v_repo_3150_);
                                    lean_dec_ref(v_name_3149_);
                                    return v___x_3234_;
                                }
                            }
                        } else {
                            v___x_3235_ = 0usize;
                            v___x_3236_ = lean_usize_of_nat(v___x_3228_);
                            v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3227_, v___x_3235_, v___x_3236_, v___x_3230_, v_a_3153_);
                            lean_dec(v_a_3227_);
                            if lean_obj_tag(v___x_3237_) == 0 {
                                lean_dec_ref_known(v___x_3237_, 1);
                                v_a_3159_ = v_a_3226_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_3226_);
                                lean_dec_ref(v_repo_3150_);
                                lean_dec_ref(v_name_3149_);
                                return v___x_3237_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_repo_3150_);
                    lean_dec_ref(v_name_3149_);
                    v_a_3238_ = lean_ctor_get(v___x_3225_, 1);
                    lean_inc(v_a_3238_);
                    lean_dec_ref_known(v___x_3225_, 2);
                    v___x_3239_ = lean_array_get_size(v_a_3238_);
                    v___x_3240_ = lean_nat_dec_lt(v___x_3223_, v___x_3239_);
                    if v___x_3240_ == 0 {
                        lean_dec(v_a_3238_);
                        v___x_3241_ = lean_box(0);
                        if v_isShared_3221_ == 0 {
                            lean_ctor_set(v___x_3220_, 0, v___x_3241_);
                            v___x_3243_ = v___x_3220_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
                            v___x_3243_ = v_reuseFailAlloc_3244_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3220_);
                        v___x_3245_ = lean_box(0);
                        v___x_3246_ = lean_nat_dec_le(v___x_3239_, v___x_3239_);
                        if v___x_3246_ == 0 {
                            if v___x_3240_ == 0 {
                                lean_dec(v_a_3238_);
                                state = 7;
                                continue;
                            } else {
                                v___x_3247_ = 0usize;
                                v___x_3248_ = lean_usize_of_nat(v___x_3239_);
                                v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3238_, v___x_3247_, v___x_3248_, v___x_3245_, v_a_3153_);
                                lean_dec(v_a_3238_);
                                if lean_obj_tag(v___x_3249_) == 0 {
                                    lean_dec_ref_known(v___x_3249_, 1);
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
                            lean_dec(v_a_3238_);
                            if lean_obj_tag(v___x_3252_) == 0 {
                                lean_dec_ref_known(v___x_3252_, 1);
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
                if lean_obj_tag(v___y_3257_) == 0 {
                    lean_dec_ref_known(v___y_3257_, 1);
                    state = 8;
                    continue;
                } else {
                    lean_dec(v_rev_x3f_3152_);
                    lean_dec_ref(v_repo_3150_);
                    lean_dec_ref(v_name_3149_);
                    return v___y_3257_;
                }
            }
            12 => {
                v___x_3259_ = lean_box(0);
                v___x_3260_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3260_, 0, v___x_3259_);
                return v___x_3260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___boxed(
    mut v_name_3294_: *mut LeanObject,
    mut v_repo_3295_: *mut LeanObject,
    mut v_url_3296_: *mut LeanObject,
    mut v_rev_x3f_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3300_: *mut LeanObject = core::ptr::null_mut();
    v_res_3300_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg(
        v_name_3294_,
        v_repo_3295_,
        v_url_3296_,
        v_rev_x3f_3297_,
        v_a_3298_,
    );
    lean_dec_ref(v_a_3298_);
    return v_res_3300_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(
    mut v_a_3301_: *mut LeanObject,
    mut v_name_3302_: *mut LeanObject,
    mut v_repo_3303_: *mut LeanObject,
    mut v_url_3304_: *mut LeanObject,
    mut v_rev_x3f_3305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: u8 = 0;
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: usize = 0;
    let mut v___x_3332_: usize = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v_unused_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: usize = 0;
    let mut v___x_3343_: usize = 0;
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3347_: u8 = 0;
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut v_unused_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: u8 = 0;
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: usize = 0;
    let mut v___x_3361_: usize = 0;
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: usize = 0;
    let mut v___x_3364_: usize = 0;
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: usize = 0;
    let mut v___x_3385_: usize = 0;
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: usize = 0;
    let mut v___x_3388_: usize = 0;
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    let mut v___x_3399_: usize = 0;
    let mut v___x_3400_: usize = 0;
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: usize = 0;
    let mut v___x_3403_: usize = 0;
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: u8 = 0;
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: usize = 0;
    let mut v___x_3428_: usize = 0;
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: usize = 0;
    let mut v___x_3431_: usize = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: usize = 0;
    let mut v___x_3441_: usize = 0;
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: usize = 0;
    let mut v___x_3444_: usize = 0;
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3413_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___closed__0;
                lean_inc_ref(v_name_3302_);
                v___x_3414_ = lean_string_append(v_name_3302_, v___x_3413_);
                v___x_3415_ = lean_string_append(v___x_3414_, v_url_3304_);
                v___x_3416_ = 1;
                v___x_3417_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_3417_, 0, v___x_3415_);
                lean_ctor_set_uint8(
                    v___x_3417_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3416_,
                );
                lean_inc_ref(v_a_3301_);
                v___x_3418_ = lean_apply_2(v_a_3301_, v___x_3417_, lean_box(0));
                v___x_3419_ = lean_unsigned_to_nat(0);
                v___x_3420_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                lean_inc_ref(v_repo_3303_);
                v___x_3421_ = l_Lake_GitRepo_clone(v_url_3304_, v_repo_3303_, v___x_3420_);
                if lean_obj_tag(v___x_3421_) == 0 {
                    v_a_3422_ = lean_ctor_get(v___x_3421_, 1);
                    lean_inc(v_a_3422_);
                    lean_dec_ref_known(v___x_3421_, 2);
                    v___x_3423_ = lean_array_get_size(v_a_3422_);
                    v___x_3424_ = lean_nat_dec_lt(v___x_3419_, v___x_3423_);
                    if v___x_3424_ == 0 {
                        lean_dec(v_a_3422_);
                        state = 8;
                        continue;
                    } else {
                        v___x_3425_ = lean_box(0);
                        v___x_3426_ = lean_nat_dec_le(v___x_3423_, v___x_3423_);
                        if v___x_3426_ == 0 {
                            if v___x_3424_ == 0 {
                                lean_dec(v_a_3422_);
                                state = 8;
                                continue;
                            } else {
                                v___x_3427_ = 0usize;
                                v___x_3428_ = lean_usize_of_nat(v___x_3423_);
                                v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3422_, v___x_3427_, v___x_3428_, v___x_3425_, v_a_3301_);
                                lean_dec(v_a_3422_);
                                if lean_obj_tag(v___x_3429_) == 0 {
                                    lean_dec_ref_known(v___x_3429_, 1);
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
                            lean_dec(v_a_3422_);
                            if lean_obj_tag(v___x_3432_) == 0 {
                                lean_dec_ref_known(v___x_3432_, 1);
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
                    v_a_3433_ = lean_ctor_get(v___x_3421_, 1);
                    lean_inc(v_a_3433_);
                    lean_dec_ref_known(v___x_3421_, 2);
                    v___x_3434_ = lean_array_get_size(v_a_3433_);
                    v___x_3435_ = lean_nat_dec_lt(v___x_3419_, v___x_3434_);
                    if v___x_3435_ == 0 {
                        lean_dec(v_a_3433_);
                        lean_dec(v_rev_x3f_3305_);
                        lean_dec_ref(v_repo_3303_);
                        lean_dec_ref(v_name_3302_);
                        v___x_3436_ = lean_box(0);
                        v___x_3437_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3437_, 0, v___x_3436_);
                        return v___x_3437_;
                    } else {
                        v___x_3438_ = lean_box(0);
                        v___x_3439_ = lean_nat_dec_le(v___x_3434_, v___x_3434_);
                        if v___x_3439_ == 0 {
                            if v___x_3435_ == 0 {
                                lean_dec(v_a_3433_);
                                lean_dec(v_rev_x3f_3305_);
                                lean_dec_ref(v_repo_3303_);
                                lean_dec_ref(v_name_3302_);
                                state = 12;
                                continue;
                            } else {
                                v___x_3440_ = 0usize;
                                v___x_3441_ = lean_usize_of_nat(v___x_3434_);
                                v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3433_, v___x_3440_, v___x_3441_, v___x_3438_, v_a_3301_);
                                lean_dec(v_a_3433_);
                                if lean_obj_tag(v___x_3442_) == 0 {
                                    lean_dec_ref_known(v___x_3442_, 1);
                                    lean_dec(v_rev_x3f_3305_);
                                    lean_dec_ref(v_repo_3303_);
                                    lean_dec_ref(v_name_3302_);
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
                            lean_dec(v_a_3433_);
                            if lean_obj_tag(v___x_3445_) == 0 {
                                lean_dec_ref_known(v___x_3445_, 1);
                                lean_dec(v_rev_x3f_3305_);
                                lean_dec_ref(v_repo_3303_);
                                lean_dec_ref(v_name_3302_);
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
                v___x_3308_ = lean_box(0);
                v___x_3309_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3309_, 0, v___x_3308_);
                return v___x_3309_;
            }
            2 => {
                v___x_3312_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
                v___x_3313_ = lean_string_append(v_name_3302_, v___x_3312_);
                v___x_3314_ = lean_string_append(v___x_3313_, v_a_3311_);
                v___x_3315_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
                v___x_3316_ = lean_string_append(v___x_3314_, v___x_3315_);
                v___x_3317_ = 1;
                v___x_3318_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_3318_, 0, v___x_3316_);
                lean_ctor_set_uint8(
                    v___x_3318_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3317_,
                );
                lean_inc_ref(v_a_3301_);
                v___x_3319_ = lean_apply_2(v_a_3301_, v___x_3318_, lean_box(0));
                v___x_3320_ = lean_unsigned_to_nat(0);
                v___x_3321_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_3322_ = l_Lake_GitRepo_checkoutDetach(v_a_3311_, v_repo_3303_, v___x_3321_);
                if lean_obj_tag(v___x_3322_) == 0 {
                    v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
                    lean_inc(v_a_3323_);
                    v_a_3324_ = lean_ctor_get(v___x_3322_, 1);
                    lean_inc(v_a_3324_);
                    lean_dec_ref_known(v___x_3322_, 2);
                    v___x_3325_ = lean_array_get_size(v_a_3324_);
                    v___x_3326_ = lean_nat_dec_lt(v___x_3320_, v___x_3325_);
                    if v___x_3326_ == 0 {
                        lean_dec(v_a_3324_);
                        v___x_3327_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3327_, 0, v_a_3323_);
                        return v___x_3327_;
                    } else {
                        v___x_3328_ = lean_box(0);
                        v___x_3329_ = lean_nat_dec_le(v___x_3325_, v___x_3325_);
                        if v___x_3329_ == 0 {
                            if v___x_3326_ == 0 {
                                lean_dec(v_a_3324_);
                                v___x_3330_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3330_, 0, v_a_3323_);
                                return v___x_3330_;
                            } else {
                                v___x_3331_ = 0usize;
                                v___x_3332_ = lean_usize_of_nat(v___x_3325_);
                                v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3324_, v___x_3331_, v___x_3332_, v___x_3328_, v_a_3301_);
                                lean_dec(v_a_3324_);
                                if lean_obj_tag(v___x_3333_) == 0 {
                                    v_isSharedCheck_3340_ = (!lean_is_exclusive(v___x_3333_)) as u8;
                                    if v_isSharedCheck_3340_ == 0 {
                                        v_unused_3341_ = lean_ctor_get(v___x_3333_, 0);
                                        lean_dec(v_unused_3341_);
                                        v___x_3335_ = v___x_3333_;
                                        v_isShared_3336_ = v_isSharedCheck_3340_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3333_);
                                        v___x_3335_ = lean_box(0);
                                        v_isShared_3336_ = v_isSharedCheck_3340_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3323_);
                                    return v___x_3333_;
                                }
                            }
                        } else {
                            v___x_3342_ = 0usize;
                            v___x_3343_ = lean_usize_of_nat(v___x_3325_);
                            v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3324_, v___x_3342_, v___x_3343_, v___x_3328_, v_a_3301_);
                            lean_dec(v_a_3324_);
                            if lean_obj_tag(v___x_3344_) == 0 {
                                v_isSharedCheck_3351_ = (!lean_is_exclusive(v___x_3344_)) as u8;
                                if v_isSharedCheck_3351_ == 0 {
                                    v_unused_3352_ = lean_ctor_get(v___x_3344_, 0);
                                    lean_dec(v_unused_3352_);
                                    v___x_3346_ = v___x_3344_;
                                    v_isShared_3347_ = v_isSharedCheck_3351_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v___x_3344_);
                                    v___x_3346_ = lean_box(0);
                                    v_isShared_3347_ = v_isSharedCheck_3351_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3323_);
                                return v___x_3344_;
                            }
                        }
                    }
                } else {
                    v_a_3353_ = lean_ctor_get(v___x_3322_, 1);
                    lean_inc(v_a_3353_);
                    lean_dec_ref_known(v___x_3322_, 2);
                    v___x_3354_ = lean_array_get_size(v_a_3353_);
                    v___x_3355_ = lean_nat_dec_lt(v___x_3320_, v___x_3354_);
                    if v___x_3355_ == 0 {
                        lean_dec(v_a_3353_);
                        v___x_3356_ = lean_box(0);
                        v___x_3357_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3357_, 0, v___x_3356_);
                        return v___x_3357_;
                    } else {
                        v___x_3358_ = lean_box(0);
                        v___x_3359_ = lean_nat_dec_le(v___x_3354_, v___x_3354_);
                        if v___x_3359_ == 0 {
                            if v___x_3355_ == 0 {
                                lean_dec(v_a_3353_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3360_ = 0usize;
                                v___x_3361_ = lean_usize_of_nat(v___x_3354_);
                                v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3353_, v___x_3360_, v___x_3361_, v___x_3358_, v_a_3301_);
                                lean_dec(v_a_3353_);
                                if lean_obj_tag(v___x_3362_) == 0 {
                                    lean_dec_ref_known(v___x_3362_, 1);
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
                            lean_dec(v_a_3353_);
                            if lean_obj_tag(v___x_3365_) == 0 {
                                lean_dec_ref_known(v___x_3365_, 1);
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
                    lean_ctor_set(v___x_3335_, 0, v_a_3323_);
                    v___x_3338_ = v___x_3335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3323_);
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
                    lean_ctor_set(v___x_3346_, 0, v_a_3323_);
                    v___x_3349_ = v___x_3346_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3323_);
                    v___x_3349_ = v_reuseFailAlloc_3350_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3349_;
            }
            7 => {
                v___x_3367_ = lean_box(0);
                v___x_3368_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3368_, 0, v___x_3367_);
                return v___x_3368_;
            }
            8 => {
                if lean_obj_tag(v_rev_x3f_3305_) == 1 {
                    v_val_3370_ = lean_ctor_get(v_rev_x3f_3305_, 0);
                    v_isSharedCheck_3405_ = (!lean_is_exclusive(v_rev_x3f_3305_)) as u8;
                    if v_isSharedCheck_3405_ == 0 {
                        v___x_3372_ = v_rev_x3f_3305_;
                        v_isShared_3373_ = v_isSharedCheck_3405_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_val_3370_);
                        lean_dec(v_rev_x3f_3305_);
                        v___x_3372_ = lean_box(0);
                        v_isShared_3373_ = v_isSharedCheck_3405_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_rev_x3f_3305_);
                    lean_dec_ref(v_repo_3303_);
                    lean_dec_ref(v_name_3302_);
                    v___x_3406_ = lean_box(0);
                    v___x_3407_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3407_, 0, v___x_3406_);
                    return v___x_3407_;
                }
            }
            9 => {
                v___x_3374_ = l_Lake_Git_defaultRemote;
                v___x_3375_ = lean_unsigned_to_nat(0);
                v___x_3376_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                lean_inc_ref(v_repo_3303_);
                v___x_3377_ = l_Lake_GitRepo_resolveRemoteRevision(
                    v_val_3370_,
                    v___x_3374_,
                    v_repo_3303_,
                    v___x_3376_,
                );
                if lean_obj_tag(v___x_3377_) == 0 {
                    lean_del_object(v___x_3372_);
                    v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
                    lean_inc(v_a_3378_);
                    v_a_3379_ = lean_ctor_get(v___x_3377_, 1);
                    lean_inc(v_a_3379_);
                    lean_dec_ref_known(v___x_3377_, 2);
                    v___x_3380_ = lean_array_get_size(v_a_3379_);
                    v___x_3381_ = lean_nat_dec_lt(v___x_3375_, v___x_3380_);
                    if v___x_3381_ == 0 {
                        lean_dec(v_a_3379_);
                        v_a_3311_ = v_a_3378_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3382_ = lean_box(0);
                        v___x_3383_ = lean_nat_dec_le(v___x_3380_, v___x_3380_);
                        if v___x_3383_ == 0 {
                            if v___x_3381_ == 0 {
                                lean_dec(v_a_3379_);
                                v_a_3311_ = v_a_3378_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3384_ = 0usize;
                                v___x_3385_ = lean_usize_of_nat(v___x_3380_);
                                v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3379_, v___x_3384_, v___x_3385_, v___x_3382_, v_a_3301_);
                                lean_dec(v_a_3379_);
                                if lean_obj_tag(v___x_3386_) == 0 {
                                    lean_dec_ref_known(v___x_3386_, 1);
                                    v_a_3311_ = v_a_3378_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v_a_3378_);
                                    lean_dec_ref(v_repo_3303_);
                                    lean_dec_ref(v_name_3302_);
                                    return v___x_3386_;
                                }
                            }
                        } else {
                            v___x_3387_ = 0usize;
                            v___x_3388_ = lean_usize_of_nat(v___x_3380_);
                            v___x_3389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3379_, v___x_3387_, v___x_3388_, v___x_3382_, v_a_3301_);
                            lean_dec(v_a_3379_);
                            if lean_obj_tag(v___x_3389_) == 0 {
                                lean_dec_ref_known(v___x_3389_, 1);
                                v_a_3311_ = v_a_3378_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_3378_);
                                lean_dec_ref(v_repo_3303_);
                                lean_dec_ref(v_name_3302_);
                                return v___x_3389_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_repo_3303_);
                    lean_dec_ref(v_name_3302_);
                    v_a_3390_ = lean_ctor_get(v___x_3377_, 1);
                    lean_inc(v_a_3390_);
                    lean_dec_ref_known(v___x_3377_, 2);
                    v___x_3391_ = lean_array_get_size(v_a_3390_);
                    v___x_3392_ = lean_nat_dec_lt(v___x_3375_, v___x_3391_);
                    if v___x_3392_ == 0 {
                        lean_dec(v_a_3390_);
                        v___x_3393_ = lean_box(0);
                        if v_isShared_3373_ == 0 {
                            lean_ctor_set(v___x_3372_, 0, v___x_3393_);
                            v___x_3395_ = v___x_3372_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
                            v___x_3395_ = v_reuseFailAlloc_3396_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3372_);
                        v___x_3397_ = lean_box(0);
                        v___x_3398_ = lean_nat_dec_le(v___x_3391_, v___x_3391_);
                        if v___x_3398_ == 0 {
                            if v___x_3392_ == 0 {
                                lean_dec(v_a_3390_);
                                state = 7;
                                continue;
                            } else {
                                v___x_3399_ = 0usize;
                                v___x_3400_ = lean_usize_of_nat(v___x_3391_);
                                v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3390_, v___x_3399_, v___x_3400_, v___x_3397_, v_a_3301_);
                                lean_dec(v_a_3390_);
                                if lean_obj_tag(v___x_3401_) == 0 {
                                    lean_dec_ref_known(v___x_3401_, 1);
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
                            lean_dec(v_a_3390_);
                            if lean_obj_tag(v___x_3404_) == 0 {
                                lean_dec_ref_known(v___x_3404_, 1);
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
                if lean_obj_tag(v___y_3409_) == 0 {
                    lean_dec_ref_known(v___y_3409_, 1);
                    state = 8;
                    continue;
                } else {
                    lean_dec(v_rev_x3f_3305_);
                    lean_dec_ref(v_repo_3303_);
                    lean_dec_ref(v_name_3302_);
                    return v___y_3409_;
                }
            }
            12 => {
                v___x_3411_ = lean_box(0);
                v___x_3412_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3412_, 0, v___x_3411_);
                return v___x_3412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0___boxed(
    mut v_a_3446_: *mut LeanObject,
    mut v_name_3447_: *mut LeanObject,
    mut v_repo_3448_: *mut LeanObject,
    mut v_url_3449_: *mut LeanObject,
    mut v_rev_x3f_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3452_: *mut LeanObject = core::ptr::null_mut();
    v_res_3452_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_3446_, v_name_3447_, v_repo_3448_, v_url_3449_, v_rev_x3f_3450_);
    lean_dec_ref(v_a_3446_);
    return v_res_3452_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(
    mut v_a_3453_: *mut LeanObject,
    mut v_name_3454_: *mut LeanObject,
    mut v_repo_3455_: *mut LeanObject,
    mut v_rev_x3f_3456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3459_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3474_: u8 = 0;
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: usize = 0;
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: usize = 0;
    let mut v___x_3483_: usize = 0;
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: usize = 0;
    let mut v___x_3504_: usize = 0;
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut v_unused_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: usize = 0;
    let mut v___x_3515_: usize = 0;
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3519_: u8 = 0;
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut v_unused_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: usize = 0;
    let mut v___x_3533_: usize = 0;
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: usize = 0;
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: u8 = 0;
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: u8 = 0;
    let mut v___x_3560_: usize = 0;
    let mut v___x_3561_: usize = 0;
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: usize = 0;
    let mut v___x_3564_: usize = 0;
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: usize = 0;
    let mut v___x_3574_: usize = 0;
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: usize = 0;
    let mut v___x_3577_: usize = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: u8 = 0;
    let mut v___x_3603_: usize = 0;
    let mut v___x_3604_: usize = 0;
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: usize = 0;
    let mut v___x_3607_: usize = 0;
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: u8 = 0;
    let mut v___x_3616_: usize = 0;
    let mut v___x_3617_: usize = 0;
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: usize = 0;
    let mut v___x_3620_: usize = 0;
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: usize = 0;
    let mut v___x_3627_: usize = 0;
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: usize = 0;
    let mut v___x_3630_: usize = 0;
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: u8 = 0;
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3639_: usize = 0;
    let mut v___x_3640_: usize = 0;
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: usize = 0;
    let mut v___x_3643_: usize = 0;
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3589_ = l_Lake_Git_defaultRemote;
                v___x_3590_ = lean_unsigned_to_nat(0);
                v___x_3591_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                lean_inc_ref(v_repo_3455_);
                v___x_3592_ = l_Lake_GitRepo_findRemoteRevision(
                    v_repo_3455_,
                    v_rev_x3f_3456_,
                    v___x_3589_,
                    v___x_3591_,
                );
                if lean_obj_tag(v___x_3592_) == 0 {
                    v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
                    lean_inc(v_a_3593_);
                    v_a_3594_ = lean_ctor_get(v___x_3592_, 1);
                    lean_inc(v_a_3594_);
                    lean_dec_ref_known(v___x_3592_, 2);
                    v___x_3622_ = lean_array_get_size(v_a_3594_);
                    v___x_3623_ = lean_nat_dec_lt(v___x_3590_, v___x_3622_);
                    if v___x_3623_ == 0 {
                        lean_dec(v_a_3594_);
                        state = 14;
                        continue;
                    } else {
                        v___x_3624_ = lean_box(0);
                        v___x_3625_ = lean_nat_dec_le(v___x_3622_, v___x_3622_);
                        if v___x_3625_ == 0 {
                            if v___x_3623_ == 0 {
                                lean_dec(v_a_3594_);
                                state = 14;
                                continue;
                            } else {
                                v___x_3626_ = 0usize;
                                v___x_3627_ = lean_usize_of_nat(v___x_3622_);
                                v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3594_, v___x_3626_, v___x_3627_, v___x_3624_, v_a_3453_);
                                lean_dec(v_a_3594_);
                                if lean_obj_tag(v___x_3628_) == 0 {
                                    lean_dec_ref_known(v___x_3628_, 1);
                                    state = 14;
                                    continue;
                                } else {
                                    lean_dec(v_a_3593_);
                                    lean_dec_ref(v_repo_3455_);
                                    lean_dec_ref(v_name_3454_);
                                    return v___x_3628_;
                                }
                            }
                        } else {
                            v___x_3629_ = 0usize;
                            v___x_3630_ = lean_usize_of_nat(v___x_3622_);
                            v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3594_, v___x_3629_, v___x_3630_, v___x_3624_, v_a_3453_);
                            lean_dec(v_a_3594_);
                            if lean_obj_tag(v___x_3631_) == 0 {
                                lean_dec_ref_known(v___x_3631_, 1);
                                state = 14;
                                continue;
                            } else {
                                lean_dec(v_a_3593_);
                                lean_dec_ref(v_repo_3455_);
                                lean_dec_ref(v_name_3454_);
                                return v___x_3631_;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_repo_3455_);
                    lean_dec_ref(v_name_3454_);
                    v_a_3632_ = lean_ctor_get(v___x_3592_, 1);
                    lean_inc(v_a_3632_);
                    lean_dec_ref_known(v___x_3592_, 2);
                    v___x_3633_ = lean_array_get_size(v_a_3632_);
                    v___x_3634_ = lean_nat_dec_lt(v___x_3590_, v___x_3633_);
                    if v___x_3634_ == 0 {
                        lean_dec(v_a_3632_);
                        v___x_3635_ = lean_box(0);
                        v___x_3636_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3636_, 0, v___x_3635_);
                        return v___x_3636_;
                    } else {
                        v___x_3637_ = lean_box(0);
                        v___x_3638_ = lean_nat_dec_le(v___x_3633_, v___x_3633_);
                        if v___x_3638_ == 0 {
                            if v___x_3634_ == 0 {
                                lean_dec(v_a_3632_);
                                state = 13;
                                continue;
                            } else {
                                v___x_3639_ = 0usize;
                                v___x_3640_ = lean_usize_of_nat(v___x_3633_);
                                v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3632_, v___x_3639_, v___x_3640_, v___x_3637_, v_a_3453_);
                                lean_dec(v_a_3632_);
                                if lean_obj_tag(v___x_3641_) == 0 {
                                    lean_dec_ref_known(v___x_3641_, 1);
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
                            lean_dec(v_a_3632_);
                            if lean_obj_tag(v___x_3644_) == 0 {
                                lean_dec_ref_known(v___x_3644_, 1);
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
                    lean_dec_ref(v_repo_3455_);
                    lean_dec_ref(v_name_3454_);
                    v___x_3460_ = lean_box(0);
                    v___x_3461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3461_, 0, v___x_3460_);
                    return v___x_3461_;
                } else {
                    v___x_3462_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
                    v___x_3463_ = lean_string_append(v_name_3454_, v___x_3462_);
                    v___x_3464_ = lean_string_append(v___x_3463_, v_repo_3455_);
                    lean_dec_ref(v_repo_3455_);
                    v___x_3465_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
                    v___x_3466_ = lean_string_append(v___x_3464_, v___x_3465_);
                    v___x_3467_ = 2;
                    v___x_3468_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3468_, 0, v___x_3466_);
                    lean_ctor_set_uint8(
                        v___x_3468_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_3467_,
                    );
                    lean_inc_ref(v_a_3453_);
                    v___x_3469_ = lean_apply_2(v_a_3453_, v___x_3468_, lean_box(0));
                    v___x_3470_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3470_, 0, v___x_3469_);
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
                    v___x_3477_ = lean_box(0);
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
                            if lean_obj_tag(v___x_3481_) == 0 {
                                lean_dec_ref_known(v___x_3481_, 1);
                                v_a_3459_ = v_val_3474_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_repo_3455_);
                                lean_dec_ref(v_name_3454_);
                                return v___x_3481_;
                            }
                        }
                    } else {
                        v___x_3482_ = 0usize;
                        v___x_3483_ = lean_usize_of_nat(v___x_3475_);
                        v___x_3484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___y_3473_, v___x_3482_, v___x_3483_, v___x_3477_, v_a_3453_);
                        if lean_obj_tag(v___x_3484_) == 0 {
                            lean_dec_ref_known(v___x_3484_, 1);
                            v_a_3459_ = v_val_3474_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_repo_3455_);
                            lean_dec_ref(v_name_3454_);
                            return v___x_3484_;
                        }
                    }
                }
            }
            3 => {
                v___x_3486_ = lean_box(0);
                v___x_3487_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3487_, 0, v___x_3486_);
                return v___x_3487_;
            }
            4 => {
                v___x_3489_ = lean_box(0);
                v___x_3490_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3490_, 0, v___x_3489_);
                return v___x_3490_;
            }
            5 => {
                v___x_3492_ = lean_unsigned_to_nat(0);
                v___x_3493_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_3494_ = l_Lake_GitRepo_clean(v_repo_3455_, v___x_3493_);
                if lean_obj_tag(v___x_3494_) == 0 {
                    v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
                    lean_inc(v_a_3495_);
                    v_a_3496_ = lean_ctor_get(v___x_3494_, 1);
                    lean_inc(v_a_3496_);
                    lean_dec_ref_known(v___x_3494_, 2);
                    v___x_3497_ = lean_array_get_size(v_a_3496_);
                    v___x_3498_ = lean_nat_dec_lt(v___x_3492_, v___x_3497_);
                    if v___x_3498_ == 0 {
                        lean_dec(v_a_3496_);
                        v___x_3499_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3499_, 0, v_a_3495_);
                        return v___x_3499_;
                    } else {
                        v___x_3500_ = lean_box(0);
                        v___x_3501_ = lean_nat_dec_le(v___x_3497_, v___x_3497_);
                        if v___x_3501_ == 0 {
                            if v___x_3498_ == 0 {
                                lean_dec(v_a_3496_);
                                v___x_3502_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3502_, 0, v_a_3495_);
                                return v___x_3502_;
                            } else {
                                v___x_3503_ = 0usize;
                                v___x_3504_ = lean_usize_of_nat(v___x_3497_);
                                v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3496_, v___x_3503_, v___x_3504_, v___x_3500_, v_a_3453_);
                                lean_dec(v_a_3496_);
                                if lean_obj_tag(v___x_3505_) == 0 {
                                    v_isSharedCheck_3512_ = (!lean_is_exclusive(v___x_3505_)) as u8;
                                    if v_isSharedCheck_3512_ == 0 {
                                        v_unused_3513_ = lean_ctor_get(v___x_3505_, 0);
                                        lean_dec(v_unused_3513_);
                                        v___x_3507_ = v___x_3505_;
                                        v_isShared_3508_ = v_isSharedCheck_3512_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3505_);
                                        v___x_3507_ = lean_box(0);
                                        v_isShared_3508_ = v_isSharedCheck_3512_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3495_);
                                    return v___x_3505_;
                                }
                            }
                        } else {
                            v___x_3514_ = 0usize;
                            v___x_3515_ = lean_usize_of_nat(v___x_3497_);
                            v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3496_, v___x_3514_, v___x_3515_, v___x_3500_, v_a_3453_);
                            lean_dec(v_a_3496_);
                            if lean_obj_tag(v___x_3516_) == 0 {
                                v_isSharedCheck_3523_ = (!lean_is_exclusive(v___x_3516_)) as u8;
                                if v_isSharedCheck_3523_ == 0 {
                                    v_unused_3524_ = lean_ctor_get(v___x_3516_, 0);
                                    lean_dec(v_unused_3524_);
                                    v___x_3518_ = v___x_3516_;
                                    v_isShared_3519_ = v_isSharedCheck_3523_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_dec(v___x_3516_);
                                    v___x_3518_ = lean_box(0);
                                    v_isShared_3519_ = v_isSharedCheck_3523_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3495_);
                                return v___x_3516_;
                            }
                        }
                    }
                } else {
                    v_a_3525_ = lean_ctor_get(v___x_3494_, 1);
                    lean_inc(v_a_3525_);
                    lean_dec_ref_known(v___x_3494_, 2);
                    v___x_3526_ = lean_array_get_size(v_a_3525_);
                    v___x_3527_ = lean_nat_dec_lt(v___x_3492_, v___x_3526_);
                    if v___x_3527_ == 0 {
                        lean_dec(v_a_3525_);
                        v___x_3528_ = lean_box(0);
                        v___x_3529_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3529_, 0, v___x_3528_);
                        return v___x_3529_;
                    } else {
                        v___x_3530_ = lean_box(0);
                        v___x_3531_ = lean_nat_dec_le(v___x_3526_, v___x_3526_);
                        if v___x_3531_ == 0 {
                            if v___x_3527_ == 0 {
                                lean_dec(v_a_3525_);
                                state = 4;
                                continue;
                            } else {
                                v___x_3532_ = 0usize;
                                v___x_3533_ = lean_usize_of_nat(v___x_3526_);
                                v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3525_, v___x_3532_, v___x_3533_, v___x_3530_, v_a_3453_);
                                lean_dec(v_a_3525_);
                                if lean_obj_tag(v___x_3534_) == 0 {
                                    lean_dec_ref_known(v___x_3534_, 1);
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
                            lean_dec(v_a_3525_);
                            if lean_obj_tag(v___x_3537_) == 0 {
                                lean_dec_ref_known(v___x_3537_, 1);
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
                    lean_ctor_set(v___x_3507_, 0, v_a_3495_);
                    v___x_3510_ = v___x_3507_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3495_);
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
                    lean_ctor_set(v___x_3518_, 0, v_a_3495_);
                    v___x_3521_ = v___x_3518_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3495_);
                    v___x_3521_ = v_reuseFailAlloc_3522_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3521_;
            }
            10 => {
                if lean_obj_tag(v___y_3539_) == 0 {
                    lean_dec_ref_known(v___y_3539_, 1);
                    state = 5;
                    continue;
                } else {
                    lean_dec_ref(v_repo_3455_);
                    return v___y_3539_;
                }
            }
            11 => {
                v___x_3543_ = lean_string_dec_eq(v_a_3542_, v___y_3541_);
                lean_dec_ref(v_a_3542_);
                if v___x_3543_ == 0 {
                    v___x_3544_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__3;
                    v___x_3545_ = lean_string_append(v_name_3454_, v___x_3544_);
                    v___x_3546_ = lean_string_append(v___x_3545_, v___y_3541_);
                    v___x_3547_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__4;
                    v___x_3548_ = lean_string_append(v___x_3546_, v___x_3547_);
                    v___x_3549_ = 1;
                    v___x_3550_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3550_, 0, v___x_3548_);
                    lean_ctor_set_uint8(
                        v___x_3550_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_3549_,
                    );
                    lean_inc_ref(v_a_3453_);
                    v___x_3551_ = lean_apply_2(v_a_3453_, v___x_3550_, lean_box(0));
                    v___x_3552_ = lean_unsigned_to_nat(0);
                    v___x_3553_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    lean_inc_ref(v_repo_3455_);
                    v___x_3554_ =
                        l_Lake_GitRepo_checkoutDetach(v___y_3541_, v_repo_3455_, v___x_3553_);
                    if lean_obj_tag(v___x_3554_) == 0 {
                        v_a_3555_ = lean_ctor_get(v___x_3554_, 1);
                        lean_inc(v_a_3555_);
                        lean_dec_ref_known(v___x_3554_, 2);
                        v___x_3556_ = lean_array_get_size(v_a_3555_);
                        v___x_3557_ = lean_nat_dec_lt(v___x_3552_, v___x_3556_);
                        if v___x_3557_ == 0 {
                            lean_dec(v_a_3555_);
                            state = 5;
                            continue;
                        } else {
                            v___x_3558_ = lean_box(0);
                            v___x_3559_ = lean_nat_dec_le(v___x_3556_, v___x_3556_);
                            if v___x_3559_ == 0 {
                                if v___x_3557_ == 0 {
                                    lean_dec(v_a_3555_);
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_3560_ = 0usize;
                                    v___x_3561_ = lean_usize_of_nat(v___x_3556_);
                                    v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3555_, v___x_3560_, v___x_3561_, v___x_3558_, v_a_3453_);
                                    lean_dec(v_a_3555_);
                                    if lean_obj_tag(v___x_3562_) == 0 {
                                        lean_dec_ref_known(v___x_3562_, 1);
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
                                lean_dec(v_a_3555_);
                                if lean_obj_tag(v___x_3565_) == 0 {
                                    lean_dec_ref_known(v___x_3565_, 1);
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
                        v_a_3566_ = lean_ctor_get(v___x_3554_, 1);
                        lean_inc(v_a_3566_);
                        lean_dec_ref_known(v___x_3554_, 2);
                        v___x_3567_ = lean_array_get_size(v_a_3566_);
                        v___x_3568_ = lean_nat_dec_lt(v___x_3552_, v___x_3567_);
                        if v___x_3568_ == 0 {
                            lean_dec(v_a_3566_);
                            lean_dec_ref(v_repo_3455_);
                            v___x_3569_ = lean_box(0);
                            v___x_3570_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3570_, 0, v___x_3569_);
                            return v___x_3570_;
                        } else {
                            v___x_3571_ = lean_box(0);
                            v___x_3572_ = lean_nat_dec_le(v___x_3567_, v___x_3567_);
                            if v___x_3572_ == 0 {
                                if v___x_3568_ == 0 {
                                    lean_dec(v_a_3566_);
                                    lean_dec_ref(v_repo_3455_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3573_ = 0usize;
                                    v___x_3574_ = lean_usize_of_nat(v___x_3567_);
                                    v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3566_, v___x_3573_, v___x_3574_, v___x_3571_, v_a_3453_);
                                    lean_dec(v_a_3566_);
                                    if lean_obj_tag(v___x_3575_) == 0 {
                                        lean_dec_ref_known(v___x_3575_, 1);
                                        lean_dec_ref(v_repo_3455_);
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
                                lean_dec(v_a_3566_);
                                if lean_obj_tag(v___x_3578_) == 0 {
                                    lean_dec_ref_known(v___x_3578_, 1);
                                    lean_dec_ref(v_repo_3455_);
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
                    lean_dec_ref(v___y_3541_);
                    lean_inc_ref(v_repo_3455_);
                    v___x_3579_ = l_Lake_GitRepo_hasNoDiff(v_repo_3455_);
                    v___x_3580_ = lean_unsigned_to_nat(0);
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
                v___x_3584_ = lean_box(0);
                v___x_3585_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3585_, 0, v___x_3584_);
                return v___x_3585_;
            }
            13 => {
                v___x_3587_ = lean_box(0);
                v___x_3588_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3588_, 0, v___x_3587_);
                return v___x_3588_;
            }
            14 => {
                lean_inc_ref(v_repo_3455_);
                v___x_3596_ = l_Lake_GitRepo_getHeadRevision(v_repo_3455_, v___x_3591_);
                if lean_obj_tag(v___x_3596_) == 0 {
                    v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
                    lean_inc(v_a_3597_);
                    v_a_3598_ = lean_ctor_get(v___x_3596_, 1);
                    lean_inc(v_a_3598_);
                    lean_dec_ref_known(v___x_3596_, 2);
                    v___x_3599_ = lean_array_get_size(v_a_3598_);
                    v___x_3600_ = lean_nat_dec_lt(v___x_3590_, v___x_3599_);
                    if v___x_3600_ == 0 {
                        lean_dec(v_a_3598_);
                        v___y_3541_ = v_a_3593_;
                        v_a_3542_ = v_a_3597_;
                        state = 11;
                        continue;
                    } else {
                        v___x_3601_ = lean_box(0);
                        v___x_3602_ = lean_nat_dec_le(v___x_3599_, v___x_3599_);
                        if v___x_3602_ == 0 {
                            if v___x_3600_ == 0 {
                                lean_dec(v_a_3598_);
                                v___y_3541_ = v_a_3593_;
                                v_a_3542_ = v_a_3597_;
                                state = 11;
                                continue;
                            } else {
                                v___x_3603_ = 0usize;
                                v___x_3604_ = lean_usize_of_nat(v___x_3599_);
                                v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3598_, v___x_3603_, v___x_3604_, v___x_3601_, v_a_3453_);
                                lean_dec(v_a_3598_);
                                if lean_obj_tag(v___x_3605_) == 0 {
                                    lean_dec_ref_known(v___x_3605_, 1);
                                    v___y_3541_ = v_a_3593_;
                                    v_a_3542_ = v_a_3597_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_dec(v_a_3597_);
                                    lean_dec(v_a_3593_);
                                    lean_dec_ref(v_repo_3455_);
                                    lean_dec_ref(v_name_3454_);
                                    return v___x_3605_;
                                }
                            }
                        } else {
                            v___x_3606_ = 0usize;
                            v___x_3607_ = lean_usize_of_nat(v___x_3599_);
                            v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3598_, v___x_3606_, v___x_3607_, v___x_3601_, v_a_3453_);
                            lean_dec(v_a_3598_);
                            if lean_obj_tag(v___x_3608_) == 0 {
                                lean_dec_ref_known(v___x_3608_, 1);
                                v___y_3541_ = v_a_3593_;
                                v_a_3542_ = v_a_3597_;
                                state = 11;
                                continue;
                            } else {
                                lean_dec(v_a_3597_);
                                lean_dec(v_a_3593_);
                                lean_dec_ref(v_repo_3455_);
                                lean_dec_ref(v_name_3454_);
                                return v___x_3608_;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_3593_);
                    lean_dec_ref(v_repo_3455_);
                    lean_dec_ref(v_name_3454_);
                    v_a_3609_ = lean_ctor_get(v___x_3596_, 1);
                    lean_inc(v_a_3609_);
                    lean_dec_ref_known(v___x_3596_, 2);
                    v___x_3610_ = lean_array_get_size(v_a_3609_);
                    v___x_3611_ = lean_nat_dec_lt(v___x_3590_, v___x_3610_);
                    if v___x_3611_ == 0 {
                        lean_dec(v_a_3609_);
                        v___x_3612_ = lean_box(0);
                        v___x_3613_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3613_, 0, v___x_3612_);
                        return v___x_3613_;
                    } else {
                        v___x_3614_ = lean_box(0);
                        v___x_3615_ = lean_nat_dec_le(v___x_3610_, v___x_3610_);
                        if v___x_3615_ == 0 {
                            if v___x_3611_ == 0 {
                                lean_dec(v_a_3609_);
                                state = 12;
                                continue;
                            } else {
                                v___x_3616_ = 0usize;
                                v___x_3617_ = lean_usize_of_nat(v___x_3610_);
                                v___x_3618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_3609_, v___x_3616_, v___x_3617_, v___x_3614_, v_a_3453_);
                                lean_dec(v_a_3609_);
                                if lean_obj_tag(v___x_3618_) == 0 {
                                    lean_dec_ref_known(v___x_3618_, 1);
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
                            lean_dec(v_a_3609_);
                            if lean_obj_tag(v___x_3621_) == 0 {
                                lean_dec_ref_known(v___x_3621_, 1);
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
    mut v_a_3645_: *mut LeanObject,
    mut v_name_3646_: *mut LeanObject,
    mut v_repo_3647_: *mut LeanObject,
    mut v_rev_x3f_3648_: *mut LeanObject,
    mut v_a_3649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3650_: *mut LeanObject = core::ptr::null_mut();
    v_res_3650_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3645_, v_name_3646_, v_repo_3647_, v_rev_x3f_3648_);
    lean_dec_ref(v_a_3645_);
    return v_res_3650_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4()
-> *mut LeanObject {
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    v___x_3655_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
    v___x_3656_ = lean_array_get_size(v___x_3655_);
    return v___x_3656_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5() -> u8 {
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: u8 = 0;
    v___x_3657_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4_once
        ),
        _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__4,
    );
    v___x_3658_ = lean_unsigned_to_nat(0);
    v___x_3659_ = lean_nat_dec_lt(v___x_3658_, v___x_3657_);
    return v___x_3659_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6() -> u8 {
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: u8 = 0;
    v___x_3660_ = lean_obj_once(
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
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: usize = 0;
    v___x_3662_ = lean_obj_once(
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
    mut v_name_3664_: *mut LeanObject,
    mut v_repo_3665_: *mut LeanObject,
    mut v_url_3666_: *mut LeanObject,
    mut v_rev_x3f_3667_: *mut LeanObject,
    mut v_a_3668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3671_: u8 = 0;
    let mut v___x_3672_: u8 = 0;
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3710_: u8 = 0;
    let mut v___x_3711_: u8 = 0;
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: u8 = 0;
    let mut v___x_3714_: usize = 0;
    let mut v___x_3715_: usize = 0;
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: usize = 0;
    let mut v___x_3718_: usize = 0;
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3706_ = l_Lake_Git_defaultRemote;
                lean_inc_ref(v_repo_3665_);
                v___x_3707_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_3706_, v_repo_3665_);
                v___x_3708_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                if lean_obj_tag(v___x_3707_) == 1 {
                    v_val_3720_ = lean_ctor_get(v___x_3707_, 0);
                    lean_inc(v_val_3720_);
                    lean_dec_ref_known(v___x_3707_, 1);
                    v___x_3721_ = lean_string_dec_eq(v_val_3720_, v_url_3666_);
                    if v___x_3721_ == 0 {
                        v___x_3722_ = lean_io_realpath(v_val_3720_);
                        if lean_obj_tag(v___x_3722_) == 0 {
                            v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
                            lean_inc(v_a_3723_);
                            lean_dec_ref_known(v___x_3722_, 1);
                            lean_inc_ref(v_url_3666_);
                            v___x_3724_ = lean_io_realpath(v_url_3666_);
                            if lean_obj_tag(v___x_3724_) == 0 {
                                v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
                                lean_inc(v_a_3725_);
                                lean_dec_ref_known(v___x_3724_, 1);
                                v___x_3726_ = lean_string_dec_eq(v_a_3723_, v_a_3725_);
                                lean_dec(v_a_3725_);
                                lean_dec(v_a_3723_);
                                v_val_3710_ = v___x_3726_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_3724_, 1);
                                lean_dec(v_a_3723_);
                                v_val_3710_ = v___x_3721_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v___x_3722_, 1);
                            v_val_3710_ = v___x_3721_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3720_);
                        v_val_3710_ = v___x_3721_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3707_);
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
                        lean_inc_ref(v_name_3664_);
                        v___x_3674_ = lean_string_append(v_name_3664_, v___x_3673_);
                        v___x_3675_ = lean_string_append(v___x_3674_, v_repo_3665_);
                        v___x_3676_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
                        v___x_3677_ = lean_string_append(v___x_3675_, v___x_3676_);
                        v___x_3678_ = 1;
                        v___x_3679_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_3679_, 0, v___x_3677_);
                        lean_ctor_set_uint8(
                            v___x_3679_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_3678_,
                        );
                        lean_inc_ref(v_a_3668_);
                        v___x_3680_ = lean_apply_2(v_a_3668_, v___x_3679_, lean_box(0));
                        v___x_3681_ = l_IO_FS_removeDirAll(v_repo_3665_);
                        if lean_obj_tag(v___x_3681_) == 0 {
                            lean_dec_ref_known(v___x_3681_, 1);
                            v___x_3682_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_3668_, v_name_3664_, v_repo_3665_, v_url_3666_, v_rev_x3f_3667_);
                            return v___x_3682_;
                        } else {
                            lean_dec(v_rev_x3f_3667_);
                            lean_dec_ref(v_url_3666_);
                            lean_dec_ref(v_repo_3665_);
                            lean_dec_ref(v_name_3664_);
                            v_a_3683_ = lean_ctor_get(v___x_3681_, 0);
                            v_isSharedCheck_3695_ = (!lean_is_exclusive(v___x_3681_)) as u8;
                            if v_isSharedCheck_3695_ == 0 {
                                v___x_3685_ = v___x_3681_;
                                v_isShared_3686_ = v_isSharedCheck_3695_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3683_);
                                lean_dec(v___x_3681_);
                                v___x_3685_ = lean_box(0);
                                v_isShared_3686_ = v_isSharedCheck_3695_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_url_3666_);
                        v___x_3696_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
                        lean_inc_ref(v_name_3664_);
                        v___x_3697_ = lean_string_append(v_name_3664_, v___x_3696_);
                        v___x_3698_ = lean_string_append(v___x_3697_, v_repo_3665_);
                        v___x_3699_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
                        v___x_3700_ = lean_string_append(v___x_3698_, v___x_3699_);
                        v___x_3701_ = 1;
                        v___x_3702_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_3702_, 0, v___x_3700_);
                        lean_ctor_set_uint8(
                            v___x_3702_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_3701_,
                        );
                        lean_inc_ref(v_a_3668_);
                        v___x_3703_ = lean_apply_2(v_a_3668_, v___x_3702_, lean_box(0));
                        v___x_3704_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3668_, v_name_3664_, v_repo_3665_, v_rev_x3f_3667_);
                        return v___x_3704_;
                    }
                } else {
                    lean_dec_ref(v_url_3666_);
                    v___x_3705_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3668_, v_name_3664_, v_repo_3665_, v_rev_x3f_3667_);
                    return v___x_3705_;
                }
            }
            2 => {
                v___x_3687_ = lean_io_error_to_string(v_a_3683_);
                v___x_3688_ = 3;
                v___x_3689_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_3689_, 0, v___x_3687_);
                lean_ctor_set_uint8(
                    v___x_3689_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3688_,
                );
                lean_inc_ref(v_a_3668_);
                v___x_3690_ = lean_apply_2(v_a_3668_, v___x_3689_, lean_box(0));
                v___x_3691_ = lean_box(0);
                if v_isShared_3686_ == 0 {
                    lean_ctor_set(v___x_3685_, 0, v___x_3691_);
                    v___x_3693_ = v___x_3685_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
                    v___x_3693_ = v_reuseFailAlloc_3694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3693_;
            }
            4 => {
                v___x_3711_ = lean_uint8_once(
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
                    v___x_3712_ = lean_box(0);
                    v___x_3713_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_3713_ == 0 {
                        if v___x_3711_ == 0 {
                            v_a_3671_ = v_val_3710_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3714_ = 0usize;
                            v___x_3715_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_3716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3708_, v___x_3714_, v___x_3715_, v___x_3712_, v_a_3668_);
                            if lean_obj_tag(v___x_3716_) == 0 {
                                lean_dec_ref_known(v___x_3716_, 1);
                                v_a_3671_ = v_val_3710_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_rev_x3f_3667_);
                                lean_dec_ref(v_url_3666_);
                                lean_dec_ref(v_repo_3665_);
                                lean_dec_ref(v_name_3664_);
                                return v___x_3716_;
                            }
                        }
                    } else {
                        v___x_3717_ = 0usize;
                        v___x_3718_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3708_, v___x_3717_, v___x_3718_, v___x_3712_, v_a_3668_);
                        if lean_obj_tag(v___x_3719_) == 0 {
                            lean_dec_ref_known(v___x_3719_, 1);
                            v_a_3671_ = v_val_3710_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_rev_x3f_3667_);
                            lean_dec_ref(v_url_3666_);
                            lean_dec_ref(v_repo_3665_);
                            lean_dec_ref(v_name_3664_);
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
    mut v_name_3728_: *mut LeanObject,
    mut v_repo_3729_: *mut LeanObject,
    mut v_url_3730_: *mut LeanObject,
    mut v_rev_x3f_3731_: *mut LeanObject,
    mut v_a_3732_: *mut LeanObject,
    mut v_a_3733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3734_: *mut LeanObject = core::ptr::null_mut();
    v_res_3734_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo(
        v_name_3728_,
        v_repo_3729_,
        v_url_3730_,
        v_rev_x3f_3731_,
        v_a_3732_,
    );
    lean_dec_ref(v_a_3732_);
    return v_res_3734_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(
    mut v_a_3735_: *mut LeanObject,
    mut v_name_3736_: *mut LeanObject,
    mut v_repo_3737_: *mut LeanObject,
    mut v_url_3738_: *mut LeanObject,
    mut v_rev_x3f_3739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3742_: u8 = 0;
    let mut v___x_3743_: u8 = 0;
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: u8 = 0;
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: u8 = 0;
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3781_: u8 = 0;
    let mut v___x_3782_: u8 = 0;
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: usize = 0;
    let mut v___x_3786_: usize = 0;
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: usize = 0;
    let mut v___x_3789_: usize = 0;
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: u8 = 0;
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3777_ = l_Lake_Git_defaultRemote;
                lean_inc_ref(v_repo_3737_);
                v___x_3778_ = l_Lake_GitRepo_getRemoteUrl_x3f(v___x_3777_, v_repo_3737_);
                v___x_3779_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                if lean_obj_tag(v___x_3778_) == 1 {
                    v_val_3791_ = lean_ctor_get(v___x_3778_, 0);
                    lean_inc(v_val_3791_);
                    lean_dec_ref_known(v___x_3778_, 1);
                    v___x_3792_ = lean_string_dec_eq(v_val_3791_, v_url_3738_);
                    if v___x_3792_ == 0 {
                        v___x_3793_ = lean_io_realpath(v_val_3791_);
                        if lean_obj_tag(v___x_3793_) == 0 {
                            v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
                            lean_inc(v_a_3794_);
                            lean_dec_ref_known(v___x_3793_, 1);
                            lean_inc_ref(v_url_3738_);
                            v___x_3795_ = lean_io_realpath(v_url_3738_);
                            if lean_obj_tag(v___x_3795_) == 0 {
                                v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
                                lean_inc(v_a_3796_);
                                lean_dec_ref_known(v___x_3795_, 1);
                                v___x_3797_ = lean_string_dec_eq(v_a_3794_, v_a_3796_);
                                lean_dec(v_a_3796_);
                                lean_dec(v_a_3794_);
                                v_val_3781_ = v___x_3797_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_3795_, 1);
                                lean_dec(v_a_3794_);
                                v_val_3781_ = v___x_3792_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v___x_3793_, 1);
                            v_val_3781_ = v___x_3792_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3791_);
                        v_val_3781_ = v___x_3792_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3778_);
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
                        lean_inc_ref(v_name_3736_);
                        v___x_3745_ = lean_string_append(v_name_3736_, v___x_3744_);
                        v___x_3746_ = lean_string_append(v___x_3745_, v_repo_3737_);
                        v___x_3747_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__1;
                        v___x_3748_ = lean_string_append(v___x_3746_, v___x_3747_);
                        v___x_3749_ = 1;
                        v___x_3750_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_3750_, 0, v___x_3748_);
                        lean_ctor_set_uint8(
                            v___x_3750_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_3749_,
                        );
                        lean_inc_ref(v_a_3735_);
                        v___x_3751_ = lean_apply_2(v_a_3735_, v___x_3750_, lean_box(0));
                        v___x_3752_ = l_IO_FS_removeDirAll(v_repo_3737_);
                        if lean_obj_tag(v___x_3752_) == 0 {
                            lean_dec_ref_known(v___x_3752_, 1);
                            v___x_3753_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_3735_, v_name_3736_, v_repo_3737_, v_url_3738_, v_rev_x3f_3739_);
                            return v___x_3753_;
                        } else {
                            lean_dec(v_rev_x3f_3739_);
                            lean_dec_ref(v_url_3738_);
                            lean_dec_ref(v_repo_3737_);
                            lean_dec_ref(v_name_3736_);
                            v_a_3754_ = lean_ctor_get(v___x_3752_, 0);
                            v_isSharedCheck_3766_ = (!lean_is_exclusive(v___x_3752_)) as u8;
                            if v_isSharedCheck_3766_ == 0 {
                                v___x_3756_ = v___x_3752_;
                                v_isShared_3757_ = v_isSharedCheck_3766_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3754_);
                                lean_dec(v___x_3752_);
                                v___x_3756_ = lean_box(0);
                                v_isShared_3757_ = v_isSharedCheck_3766_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_url_3738_);
                        v___x_3767_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__2;
                        lean_inc_ref(v_name_3736_);
                        v___x_3768_ = lean_string_append(v_name_3736_, v___x_3767_);
                        v___x_3769_ = lean_string_append(v___x_3768_, v_repo_3737_);
                        v___x_3770_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__3;
                        v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
                        v___x_3772_ = 1;
                        v___x_3773_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_3773_, 0, v___x_3771_);
                        lean_ctor_set_uint8(
                            v___x_3773_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_3772_,
                        );
                        lean_inc_ref(v_a_3735_);
                        v___x_3774_ = lean_apply_2(v_a_3735_, v___x_3773_, lean_box(0));
                        v___x_3775_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3735_, v_name_3736_, v_repo_3737_, v_rev_x3f_3739_);
                        return v___x_3775_;
                    }
                } else {
                    lean_dec_ref(v_url_3738_);
                    v___x_3776_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__1(v_a_3735_, v_name_3736_, v_repo_3737_, v_rev_x3f_3739_);
                    return v___x_3776_;
                }
            }
            2 => {
                v___x_3758_ = lean_io_error_to_string(v_a_3754_);
                v___x_3759_ = 3;
                v___x_3760_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_3760_, 0, v___x_3758_);
                lean_ctor_set_uint8(
                    v___x_3760_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3759_,
                );
                lean_inc_ref(v_a_3735_);
                v___x_3761_ = lean_apply_2(v_a_3735_, v___x_3760_, lean_box(0));
                v___x_3762_ = lean_box(0);
                if v_isShared_3757_ == 0 {
                    lean_ctor_set(v___x_3756_, 0, v___x_3762_);
                    v___x_3764_ = v___x_3756_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
                    v___x_3764_ = v_reuseFailAlloc_3765_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3764_;
            }
            4 => {
                v___x_3782_ = lean_uint8_once(
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
                    v___x_3783_ = lean_box(0);
                    v___x_3784_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_3784_ == 0 {
                        if v___x_3782_ == 0 {
                            v_a_3742_ = v_val_3781_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3785_ = 0usize;
                            v___x_3786_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3779_, v___x_3785_, v___x_3786_, v___x_3783_, v_a_3735_);
                            if lean_obj_tag(v___x_3787_) == 0 {
                                lean_dec_ref_known(v___x_3787_, 1);
                                v_a_3742_ = v_val_3781_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_rev_x3f_3739_);
                                lean_dec_ref(v_url_3738_);
                                lean_dec_ref(v_repo_3737_);
                                lean_dec_ref(v_name_3736_);
                                return v___x_3787_;
                            }
                        }
                    } else {
                        v___x_3788_ = 0usize;
                        v___x_3789_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_3790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3779_, v___x_3788_, v___x_3789_, v___x_3783_, v_a_3735_);
                        if lean_obj_tag(v___x_3790_) == 0 {
                            lean_dec_ref_known(v___x_3790_, 1);
                            v_a_3742_ = v_val_3781_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_rev_x3f_3739_);
                            lean_dec_ref(v_url_3738_);
                            lean_dec_ref(v_repo_3737_);
                            lean_dec_ref(v_name_3736_);
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
    mut v_a_3799_: *mut LeanObject,
    mut v_name_3800_: *mut LeanObject,
    mut v_repo_3801_: *mut LeanObject,
    mut v_url_3802_: *mut LeanObject,
    mut v_rev_x3f_3803_: *mut LeanObject,
    mut v_a_3804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3805_: *mut LeanObject = core::ptr::null_mut();
    v_res_3805_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_3799_, v_name_3800_, v_repo_3801_, v_url_3802_, v_rev_x3f_3803_);
    lean_dec_ref(v_a_3799_);
    return v_res_3805_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(
    mut v_name_3806_: *mut LeanObject,
    mut v_repo_3807_: *mut LeanObject,
    mut v_url_3808_: *mut LeanObject,
    mut v_rev_x3f_3809_: *mut LeanObject,
    mut v_a_3810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: u8 = 0;
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: u8 = 0;
    let mut v___x_3820_: usize = 0;
    let mut v___x_3821_: usize = 0;
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: usize = 0;
    let mut v___x_3824_: usize = 0;
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3812_ = l_System_FilePath_isDir(v_repo_3807_);
                v___x_3816_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_3817_ = lean_uint8_once(
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
                    v___x_3818_ = lean_box(0);
                    v___x_3819_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_3819_ == 0 {
                        if v___x_3817_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3820_ = 0usize;
                            v___x_3821_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3816_, v___x_3820_, v___x_3821_, v___x_3818_, v_a_3810_);
                            if lean_obj_tag(v___x_3822_) == 0 {
                                lean_dec_ref_known(v___x_3822_, 1);
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_rev_x3f_3809_);
                                lean_dec_ref(v_url_3808_);
                                lean_dec_ref(v_repo_3807_);
                                lean_dec_ref(v_name_3806_);
                                return v___x_3822_;
                            }
                        }
                    } else {
                        v___x_3823_ = 0usize;
                        v___x_3824_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_3816_, v___x_3823_, v___x_3824_, v___x_3818_, v_a_3810_);
                        if lean_obj_tag(v___x_3825_) == 0 {
                            lean_dec_ref_known(v___x_3825_, 1);
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_rev_x3f_3809_);
                            lean_dec_ref(v_url_3808_);
                            lean_dec_ref(v_repo_3807_);
                            lean_dec_ref(v_name_3806_);
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
    mut v_name_3826_: *mut LeanObject,
    mut v_repo_3827_: *mut LeanObject,
    mut v_url_3828_: *mut LeanObject,
    mut v_rev_x3f_3829_: *mut LeanObject,
    mut v_a_3830_: *mut LeanObject,
    mut v_a_3831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3832_: *mut LeanObject = core::ptr::null_mut();
    v_res_3832_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo(
        v_name_3826_,
        v_repo_3827_,
        v_url_3828_,
        v_rev_x3f_3829_,
        v_a_3830_,
    );
    lean_dec_ref(v_a_3830_);
    return v_res_3832_;
}
pub unsafe fn _init_l_Lake_instInhabitedMaterializedDep_default___closed__4() -> *mut LeanObject {
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    v___x_3839_ = l_Lake_instInhabitedPackageEntry_default;
    v___x_3840_ = l_Lake_instInhabitedMaterializedDep_default___closed__3;
    v___x_3841_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
    v___x_3842_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3842_, 0, v___x_3841_);
    lean_ctor_set(v___x_3842_, 1, v___x_3841_);
    lean_ctor_set(v___x_3842_, 2, v___x_3841_);
    lean_ctor_set(v___x_3842_, 3, v___x_3840_);
    lean_ctor_set(v___x_3842_, 4, v___x_3839_);
    return v___x_3842_;
}
pub unsafe fn _init_l_Lake_instInhabitedMaterializedDep_default() -> *mut LeanObject {
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    v___x_3843_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedMaterializedDep_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedMaterializedDep_default___closed__4_once),
        _init_l_Lake_instInhabitedMaterializedDep_default___closed__4,
    );
    return v___x_3843_;
}
pub unsafe fn _init_l_Lake_instInhabitedMaterializedDep() -> *mut LeanObject {
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    v___x_3844_ = l_Lake_instInhabitedMaterializedDep_default;
    return v___x_3844_;
}
pub unsafe fn l_Lake_MaterializedDep_name(mut v_self_3845_: *mut LeanObject) -> *mut LeanObject {
    let mut v_manifestEntry_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3847_: *mut LeanObject = core::ptr::null_mut();
    v_manifestEntry_3846_ = lean_ctor_get(v_self_3845_, 4);
    v_name_3847_ = lean_ctor_get(v_manifestEntry_3846_, 0);
    lean_inc(v_name_3847_);
    return v_name_3847_;
}
pub unsafe fn l_Lake_MaterializedDep_name___boxed(
    mut v_self_3848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3849_: *mut LeanObject = core::ptr::null_mut();
    v_res_3849_ = l_Lake_MaterializedDep_name(v_self_3848_);
    lean_dec_ref(v_self_3848_);
    return v_res_3849_;
}
pub unsafe fn l_Lake_MaterializedDep_prettyName(
    mut v_self_3850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_manifestEntry_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v_manifestEntry_3851_ = lean_ctor_get(v_self_3850_, 4);
    lean_inc_ref(v_manifestEntry_3851_);
    lean_dec_ref(v_self_3850_);
    v_name_3852_ = lean_ctor_get(v_manifestEntry_3851_, 0);
    lean_inc(v_name_3852_);
    lean_dec_ref(v_manifestEntry_3851_);
    v___x_3853_ = 0;
    v___x_3854_ = l_Lean_Name_toString(v_name_3852_, v___x_3853_);
    return v___x_3854_;
}
pub unsafe fn l_Lake_MaterializedDep_scope(mut v_self_3855_: *mut LeanObject) -> *mut LeanObject {
    let mut v_manifestEntry_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_3857_: *mut LeanObject = core::ptr::null_mut();
    v_manifestEntry_3856_ = lean_ctor_get(v_self_3855_, 4);
    v_scope_3857_ = lean_ctor_get(v_manifestEntry_3856_, 1);
    lean_inc_ref(v_scope_3857_);
    return v_scope_3857_;
}
pub unsafe fn l_Lake_MaterializedDep_scope___boxed(
    mut v_self_3858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3859_: *mut LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Lake_MaterializedDep_scope(v_self_3858_);
    lean_dec_ref(v_self_3858_);
    return v_res_3859_;
}
pub unsafe fn l_Lake_MaterializedDep_relManifestFile_x3f(
    mut v_self_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_manifestEntry_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3862_: *mut LeanObject = core::ptr::null_mut();
    v_manifestEntry_3861_ = lean_ctor_get(v_self_3860_, 4);
    v_manifestFile_x3f_3862_ = lean_ctor_get(v_manifestEntry_3861_, 3);
    lean_inc(v_manifestFile_x3f_3862_);
    return v_manifestFile_x3f_3862_;
}
pub unsafe fn l_Lake_MaterializedDep_relManifestFile_x3f___boxed(
    mut v_self_3863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3864_: *mut LeanObject = core::ptr::null_mut();
    v_res_3864_ = l_Lake_MaterializedDep_relManifestFile_x3f(v_self_3863_);
    lean_dec_ref(v_self_3863_);
    return v_res_3864_;
}
pub unsafe fn l_Lake_MaterializedDep_relManifestFile(
    mut v_self_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_manifestEntry_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3867_: *mut LeanObject = core::ptr::null_mut();
    v_manifestEntry_3866_ = lean_ctor_get(v_self_3865_, 4);
    v_manifestFile_x3f_3867_ = lean_ctor_get(v_manifestEntry_3866_, 3);
    if lean_obj_tag(v_manifestFile_x3f_3867_) == 0 {
        let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
        v___x_3868_ = l_Lake_defaultManifestFile;
        return v___x_3868_;
    } else {
        let mut v_val_3869_: *mut LeanObject = core::ptr::null_mut();
        v_val_3869_ = lean_ctor_get(v_manifestFile_x3f_3867_, 0);
        lean_inc(v_val_3869_);
        return v_val_3869_;
    }
}
pub unsafe fn l_Lake_MaterializedDep_relManifestFile___boxed(
    mut v_self_3870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3871_: *mut LeanObject = core::ptr::null_mut();
    v_res_3871_ = l_Lake_MaterializedDep_relManifestFile(v_self_3870_);
    lean_dec_ref(v_self_3870_);
    return v_res_3871_;
}
pub unsafe fn l_Lake_MaterializedDep_manifestFile(
    mut v_self_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_manifestEntry_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3874_: *mut LeanObject = core::ptr::null_mut();
    v_manifestEntry_3873_ = lean_ctor_get(v_self_3872_, 4);
    v_manifestFile_x3f_3874_ = lean_ctor_get(v_manifestEntry_3873_, 3);
    if lean_obj_tag(v_manifestFile_x3f_3874_) == 0 {
        let mut v_pkgDir_3875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
        v_pkgDir_3875_ = lean_ctor_get(v_self_3872_, 0);
        lean_inc_ref(v_pkgDir_3875_);
        lean_dec_ref(v_self_3872_);
        v___x_3876_ = l_Lake_defaultManifestFile;
        v___x_3877_ = l_Lake_joinRelative(v_pkgDir_3875_, v___x_3876_);
        return v___x_3877_;
    } else {
        let mut v_pkgDir_3878_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_3879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_manifestFile_x3f_3874_);
        v_pkgDir_3878_ = lean_ctor_get(v_self_3872_, 0);
        lean_inc_ref(v_pkgDir_3878_);
        lean_dec_ref(v_self_3872_);
        v_val_3879_ = lean_ctor_get(v_manifestFile_x3f_3874_, 0);
        lean_inc(v_val_3879_);
        lean_dec_ref_known(v_manifestFile_x3f_3874_, 1);
        v___x_3880_ = l_Lake_joinRelative(v_pkgDir_3878_, v_val_3879_);
        return v___x_3880_;
    }
}
pub unsafe fn l_Lake_MaterializedDep_relConfigFile(
    mut v_self_3881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_manifestEntry_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_configFile_3883_: *mut LeanObject = core::ptr::null_mut();
    v_manifestEntry_3882_ = lean_ctor_get(v_self_3881_, 4);
    v_configFile_3883_ = lean_ctor_get(v_manifestEntry_3882_, 2);
    lean_inc_ref(v_configFile_3883_);
    return v_configFile_3883_;
}
pub unsafe fn l_Lake_MaterializedDep_relConfigFile___boxed(
    mut v_self_3884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3885_: *mut LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Lake_MaterializedDep_relConfigFile(v_self_3884_);
    lean_dec_ref(v_self_3884_);
    return v_res_3885_;
}
pub unsafe fn l_Lake_MaterializedDep_configFile(
    mut v_self_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_manifestEntry_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_configFile_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    v_manifestEntry_3887_ = lean_ctor_get(v_self_3886_, 4);
    lean_inc_ref(v_manifestEntry_3887_);
    v_pkgDir_3888_ = lean_ctor_get(v_self_3886_, 0);
    lean_inc_ref(v_pkgDir_3888_);
    lean_dec_ref(v_self_3886_);
    v_configFile_3889_ = lean_ctor_get(v_manifestEntry_3887_, 2);
    lean_inc_ref(v_configFile_3889_);
    lean_dec_ref(v_manifestEntry_3887_);
    v___x_3890_ = l_Lake_joinRelative(v_pkgDir_3888_, v_configFile_3889_);
    return v___x_3890_;
}
pub unsafe fn l_Lake_MaterializedDep_fixedToolchain(mut v_self_3891_: *mut LeanObject) -> u8 {
    let mut v_manifest_x3f_3892_: *mut LeanObject = core::ptr::null_mut();
    v_manifest_x3f_3892_ = lean_ctor_get(v_self_3891_, 3);
    if lean_obj_tag(v_manifest_x3f_3892_) == 1 {
        let mut v_a_3893_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fixedToolchain_3894_: u8 = 0;
        v_a_3893_ = lean_ctor_get(v_manifest_x3f_3892_, 0);
        v_fixedToolchain_3894_ = lean_ctor_get_uint8(
            v_a_3893_,
            (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        );
        return v_fixedToolchain_3894_;
    } else {
        let mut v___x_3895_: u8 = 0;
        v___x_3895_ = 0;
        return v___x_3895_;
    }
}
pub unsafe fn l_Lake_MaterializedDep_fixedToolchain___boxed(
    mut v_self_3896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3897_: u8 = 0;
    let mut v_r_3898_: *mut LeanObject = core::ptr::null_mut();
    v_res_3897_ = l_Lake_MaterializedDep_fixedToolchain(v_self_3896_);
    lean_dec_ref(v_self_3896_);
    v_r_3898_ = lean_box((v_res_3897_) as usize);
    return v_r_3898_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(
    mut v_x_3899_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3899_) {
        0 => {
            let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
            v___x_3900_ = lean_unsigned_to_nat(0);
            return v___x_3900_;
        }
        1 => {
            let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
            v___x_3901_ = lean_unsigned_to_nat(1);
            return v___x_3901_;
        }
        _ => {
            let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
            v___x_3902_ = lean_unsigned_to_nat(2);
            return v___x_3902_;
        }
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx___boxed(
    mut v_x_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3904_: *mut LeanObject = core::ptr::null_mut();
    v_res_3904_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorIdx(v_x_3903_);
    lean_dec(v_x_3903_);
    return v_res_3904_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
    mut v_t_3905_: *mut LeanObject,
    mut v_k_3906_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_3905_) == 0 {
        return v_k_3906_;
    } else {
        let mut v_rev_3907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
        v_rev_3907_ = lean_ctor_get(v_t_3905_, 0);
        lean_inc_ref(v_rev_3907_);
        lean_dec(v_t_3905_);
        v___x_3908_ = lean_apply_1(v_k_3906_, v_rev_3907_);
        return v___x_3908_;
    }
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(
    mut v_motive_3909_: *mut LeanObject,
    mut v_ctorIdx_3910_: *mut LeanObject,
    mut v_t_3911_: *mut LeanObject,
    mut v_h_3912_: *mut LeanObject,
    mut v_k_3913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    v___x_3914_ =
        l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(v_t_3911_, v_k_3913_);
    return v___x_3914_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___boxed(
    mut v_motive_3915_: *mut LeanObject,
    mut v_ctorIdx_3916_: *mut LeanObject,
    mut v_t_3917_: *mut LeanObject,
    mut v_h_3918_: *mut LeanObject,
    mut v_k_3919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3920_: *mut LeanObject = core::ptr::null_mut();
    v_res_3920_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim(
        v_motive_3915_,
        v_ctorIdx_3916_,
        v_t_3917_,
        v_h_3918_,
        v_k_3919_,
    );
    lean_dec(v_ctorIdx_3916_);
    return v_res_3920_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim___redArg(
    mut v_t_3921_: *mut LeanObject,
    mut v_none_3922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    v___x_3923_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3921_,
        v_none_3922_,
    );
    return v___x_3923_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_none_elim(
    mut v_motive_3924_: *mut LeanObject,
    mut v_t_3925_: *mut LeanObject,
    mut v_h_3926_: *mut LeanObject,
    mut v_none_3927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    v___x_3928_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3925_,
        v_none_3927_,
    );
    return v___x_3928_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim___redArg(
    mut v_t_3929_: *mut LeanObject,
    mut v_git_3930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    v___x_3931_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3929_,
        v_git_3930_,
    );
    return v___x_3931_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_git_elim(
    mut v_motive_3932_: *mut LeanObject,
    mut v_t_3933_: *mut LeanObject,
    mut v_h_3934_: *mut LeanObject,
    mut v_git_3935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    v___x_3936_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3933_,
        v_git_3935_,
    );
    return v___x_3936_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim___redArg(
    mut v_t_3937_: *mut LeanObject,
    mut v_ver_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    v___x_3939_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3937_,
        v_ver_3938_,
    );
    return v___x_3939_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_InputVer_ver_elim(
    mut v_motive_3940_: *mut LeanObject,
    mut v_t_3941_: *mut LeanObject,
    mut v_h_3942_: *mut LeanObject,
    mut v_ver_3943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    v___x_3944_ = l___private_Lake_Load_Materialize_0__Lake_InputVer_ctorElim___redArg(
        v_t_3941_,
        v_ver_3943_,
    );
    return v___x_3944_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(
    mut v_scope_3953_: *mut LeanObject,
    mut v_name_3954_: *mut LeanObject,
    mut v_ver_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v_ver_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v_toString_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_ver_3955_) {
                0 => {
                    v___x_3979_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                    v_fst_3957_ = v___x_3979_;
                    v_snd_3958_ = v___x_3979_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_rev_3980_ = lean_ctor_get(v_ver_3955_, 0);
                    v_isSharedCheck_3995_ = (!lean_is_exclusive(v_ver_3955_)) as u8;
                    if v_isSharedCheck_3995_ == 0 {
                        v___x_3982_ = v_ver_3955_;
                        v_isShared_3983_ = v_isSharedCheck_3995_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_rev_3980_);
                        lean_dec(v_ver_3955_);
                        v___x_3982_ = lean_box(0);
                        v_isShared_3983_ = v_isSharedCheck_3995_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v_ver_3996_ = lean_ctor_get(v_ver_3955_, 0);
                    v_isSharedCheck_4012_ = (!lean_is_exclusive(v_ver_3955_)) as u8;
                    if v_isSharedCheck_4012_ == 0 {
                        v___x_3998_ = v_ver_3955_;
                        v_isShared_3999_ = v_isSharedCheck_4012_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_ver_3996_);
                        lean_dec(v_ver_3955_);
                        v___x_3998_ = lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4012_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3959_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                lean_inc_ref(v_scope_3953_);
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
                lean_dec_ref(v_fst_3957_);
                v___x_3970_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__3;
                v___x_3971_ = lean_string_append(v___x_3969_, v___x_3970_);
                v___x_3972_ = lean_string_append(v___x_3971_, v_scope_3953_);
                lean_dec_ref(v_scope_3953_);
                v___x_3973_ = lean_string_append(v___x_3972_, v___x_3959_);
                v___x_3974_ = lean_string_append(v___x_3973_, v_name_3954_);
                v___x_3975_ = lean_string_append(v___x_3974_, v___x_3967_);
                v___x_3976_ = lean_string_append(v___x_3975_, v_snd_3958_);
                lean_dec_ref(v_snd_3958_);
                v___x_3977_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__4;
                v___x_3978_ = lean_string_append(v___x_3976_, v___x_3977_);
                return v___x_3978_;
            }
            2 => {
                v___x_3984_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
                v___x_3985_ = l_String_quote(v_rev_3980_);
                if v_isShared_3983_ == 0 {
                    lean_ctor_set_tag(v___x_3982_, 3);
                    lean_ctor_set(v___x_3982_, 0, v___x_3985_);
                    v___x_3987_ = v___x_3982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3985_);
                    v___x_3987_ = v_reuseFailAlloc_3994_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3988_ = l_Std_Format_defWidth;
                v___x_3989_ = lean_unsigned_to_nat(0);
                v___x_3990_ =
                    l_Std_Format_pretty(v___x_3987_, v___x_3988_, v___x_3989_, v___x_3989_);
                v___x_3991_ = lean_string_append(v___x_3984_, v___x_3990_);
                v___x_3992_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__6;
                v___x_3993_ = lean_string_append(v___x_3992_, v___x_3990_);
                lean_dec_ref(v___x_3990_);
                v_fst_3957_ = v___x_3991_;
                v_snd_3958_ = v___x_3993_;
                state = 1;
                continue;
            }
            4 => {
                v_toString_4000_ = lean_ctor_get(v_ver_3996_, 0);
                lean_inc_ref(v_toString_4000_);
                lean_dec_ref(v_ver_3996_);
                v___x_4001_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__5;
                v___x_4002_ = l_String_quote(v_toString_4000_);
                if v_isShared_3999_ == 0 {
                    lean_ctor_set_tag(v___x_3998_, 3);
                    lean_ctor_set(v___x_3998_, 0, v___x_4002_);
                    v___x_4004_ = v___x_3998_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4002_);
                    v___x_4004_ = v_reuseFailAlloc_4011_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4005_ = l_Std_Format_defWidth;
                v___x_4006_ = lean_unsigned_to_nat(0);
                v___x_4007_ =
                    l_Std_Format_pretty(v___x_4004_, v___x_4005_, v___x_4006_, v___x_4006_);
                v___x_4008_ = lean_string_append(v___x_4001_, v___x_4007_);
                v___x_4009_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__7;
                v___x_4010_ = lean_string_append(v___x_4009_, v___x_4007_);
                lean_dec_ref(v___x_4007_);
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
    mut v_scope_4013_: *mut LeanObject,
    mut v_name_4014_: *mut LeanObject,
    mut v_ver_4015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4016_: *mut LeanObject = core::ptr::null_mut();
    v_res_4016_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(
        v_scope_4013_,
        v_name_4014_,
        v_ver_4015_,
    );
    lean_dec_ref(v_name_4014_);
    return v_res_4016_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(
    mut v_x_4017_: *mut LeanObject,
    mut v___y_4018_: *mut LeanObject,
    mut v___y_4019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___y_4019_);
    v___x_4021_ = lean_apply_2(v___y_4019_, v___y_4018_, lean_box(0));
    v___x_4022_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4022_, 0, v___x_4021_);
    return v___x_4022_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0___boxed(
    mut v_x_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4027_: *mut LeanObject = core::ptr::null_mut();
    v_res_4027_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___lam__0(
        v_x_4023_,
        v___y_4024_,
        v___y_4025_,
    );
    lean_dec_ref(v___y_4025_);
    return v_res_4027_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__0()
-> *mut LeanObject {
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    v___x_4028_ = l_instMonadEIO(lean_box(0));
    return v___x_4028_;
}
pub unsafe fn _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1()
-> *mut LeanObject {
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    v___x_4029_ = lean_obj_once(
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
    mut v_dep_4033_: *mut LeanObject,
    mut v_inherited_4034_: u8,
    mut v_wsDir_4035_: *mut LeanObject,
    mut v_name_4036_: *mut LeanObject,
    mut v_relPkgDir_4037_: *mut LeanObject,
    mut v_remoteUrl_4038_: *mut LeanObject,
    mut v_src_4039_: *mut LeanObject,
    mut v_a_4040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut v_unused_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: usize = 0;
    let mut v___x_4076_: usize = 0;
    let mut v___x_2388__overap_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4082_: u8 = 0;
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v___x_4087_: usize = 0;
    let mut v___x_4088_: usize = 0;
    let mut v___x_2398__overap_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4094_: u8 = 0;
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_a_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4110_: u8 = 0;
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v_a_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4122_: u8 = 0;
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: u8 = 0;
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: u8 = 0;
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    let mut v___x_4138_: usize = 0;
    let mut v___x_4139_: usize = 0;
    let mut v___x_2450__overap_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut v___x_4150_: usize = 0;
    let mut v___x_4151_: usize = 0;
    let mut v___x_2460__overap_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4157_: u8 = 0;
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4161_: u8 = 0;
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: u8 = 0;
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_relPkgDir_4037_);
                v_pkgDir_4061_ = l_Lake_joinRelative(v_wsDir_4035_, v_relPkgDir_4037_);
                v___x_4062_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once), _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
                lean_inc_ref(v_pkgDir_4061_);
                v___x_4063_ = l_Lake_resolvePath(v_pkgDir_4061_);
                v___f_4064_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2;
                v___x_4131_ = lean_unsigned_to_nat(0);
                v___x_4132_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4162_ = lean_string_utf8_byte_size(v___x_4063_);
                v___x_4163_ = lean_nat_dec_eq(v___x_4162_, v___x_4131_);
                if v___x_4163_ == 0 {
                    v___x_4164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4164_, 0, v___x_4063_);
                    v_val_4134_ = v___x_4164_;
                    state = 14;
                    continue;
                } else {
                    lean_dec_ref(v___x_4063_);
                    v___x_4165_ = lean_box(0);
                    v_val_4134_ = v___x_4165_;
                    state = 14;
                    continue;
                }
            }
            1 => {
                v_name_4045_ = lean_ctor_get(v_dep_4033_, 0);
                v_scope_4046_ = lean_ctor_get(v_dep_4033_, 1);
                v_isSharedCheck_4057_ = (!lean_is_exclusive(v_dep_4033_)) as u8;
                if v_isSharedCheck_4057_ == 0 {
                    v_unused_4058_ = lean_ctor_get(v_dep_4033_, 4);
                    lean_dec(v_unused_4058_);
                    v_unused_4059_ = lean_ctor_get(v_dep_4033_, 3);
                    lean_dec(v_unused_4059_);
                    v_unused_4060_ = lean_ctor_get(v_dep_4033_, 2);
                    lean_dec(v_unused_4060_);
                    v___x_4048_ = v_dep_4033_;
                    v_isShared_4049_ = v_isSharedCheck_4057_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_scope_4046_);
                    lean_inc(v_name_4045_);
                    lean_dec(v_dep_4033_);
                    v___x_4048_ = lean_box(0);
                    v_isShared_4049_ = v_isSharedCheck_4057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4050_ = l_Lake_defaultConfigFile;
                v___x_4051_ = lean_box(0);
                v___x_4052_ = lean_alloc_ctor(0, 5, (1) as u32);
                lean_ctor_set(v___x_4052_, 0, v_name_4045_);
                lean_ctor_set(v___x_4052_, 1, v_scope_4046_);
                lean_ctor_set(v___x_4052_, 2, v___x_4050_);
                lean_ctor_set(v___x_4052_, 3, v___x_4051_);
                lean_ctor_set(v___x_4052_, 4, v_src_4039_);
                lean_ctor_set_uint8(
                    v___x_4052_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v_inherited_4034_,
                );
                if v_isShared_4049_ == 0 {
                    lean_ctor_set(v___x_4048_, 4, v___x_4052_);
                    lean_ctor_set(v___x_4048_, 3, v_a_4044_);
                    lean_ctor_set(v___x_4048_, 2, v_remoteUrl_4038_);
                    lean_ctor_set(v___x_4048_, 1, v_relPkgDir_4037_);
                    lean_ctor_set(v___x_4048_, 0, v___y_4043_);
                    v___x_4054_ = v___x_4048_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___y_4043_);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_relPkgDir_4037_);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_remoteUrl_4038_);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 3, v_a_4044_);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 4, v___x_4052_);
                    v___x_4054_ = v_reuseFailAlloc_4056_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4055_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4055_, 0, v___x_4054_);
                return v___x_4055_;
            }
            4 => {
                v___x_4071_ = lean_array_get_size(v___y_4067_);
                v___x_4072_ = lean_nat_dec_lt(v___y_4066_, v___x_4071_);
                if v___x_4072_ == 0 {
                    lean_dec_ref(v___y_4069_);
                    v___y_4043_ = v___y_4068_;
                    v_a_4044_ = v_val_4070_;
                    state = 1;
                    continue;
                } else {
                    v___x_4073_ = lean_box(0);
                    v___x_4074_ = lean_nat_dec_le(v___x_4071_, v___x_4071_);
                    if v___x_4074_ == 0 {
                        if v___x_4072_ == 0 {
                            lean_dec_ref(v___y_4069_);
                            v___y_4043_ = v___y_4068_;
                            v_a_4044_ = v_val_4070_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4075_ = 0usize;
                            v___x_4076_ = lean_usize_of_nat(v___x_4071_);
                            lean_inc_ref(v___y_4067_);
                            v___x_2388__overap_4077_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___y_4069_,
                                    v___f_4064_,
                                    v___y_4067_,
                                    v___x_4075_,
                                    v___x_4076_,
                                    v___x_4073_,
                                );
                            lean_inc_ref(v_a_4040_);
                            v___x_4078_ =
                                lean_apply_2(v___x_2388__overap_4077_, v_a_4040_, lean_box(0));
                            if lean_obj_tag(v___x_4078_) == 0 {
                                lean_dec_ref_known(v___x_4078_, 1);
                                v___y_4043_ = v___y_4068_;
                                v_a_4044_ = v_val_4070_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_val_4070_);
                                lean_dec_ref(v___y_4068_);
                                lean_dec_ref(v_src_4039_);
                                lean_dec_ref(v_remoteUrl_4038_);
                                lean_dec_ref(v_relPkgDir_4037_);
                                lean_dec_ref(v_dep_4033_);
                                v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
                                v_isSharedCheck_4086_ = (!lean_is_exclusive(v___x_4078_)) as u8;
                                if v_isSharedCheck_4086_ == 0 {
                                    v___x_4081_ = v___x_4078_;
                                    v_isShared_4082_ = v_isSharedCheck_4086_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_4079_);
                                    lean_dec(v___x_4078_);
                                    v___x_4081_ = lean_box(0);
                                    v_isShared_4082_ = v_isSharedCheck_4086_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4087_ = 0usize;
                        v___x_4088_ = lean_usize_of_nat(v___x_4071_);
                        lean_inc_ref(v___y_4067_);
                        v___x_2398__overap_4089_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___y_4069_,
                                v___f_4064_,
                                v___y_4067_,
                                v___x_4087_,
                                v___x_4088_,
                                v___x_4073_,
                            );
                        lean_inc_ref(v_a_4040_);
                        v___x_4090_ =
                            lean_apply_2(v___x_2398__overap_4089_, v_a_4040_, lean_box(0));
                        if lean_obj_tag(v___x_4090_) == 0 {
                            lean_dec_ref_known(v___x_4090_, 1);
                            v___y_4043_ = v___y_4068_;
                            v_a_4044_ = v_val_4070_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_val_4070_);
                            lean_dec_ref(v___y_4068_);
                            lean_dec_ref(v_src_4039_);
                            lean_dec_ref(v_remoteUrl_4038_);
                            lean_dec_ref(v_relPkgDir_4037_);
                            lean_dec_ref(v_dep_4033_);
                            v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
                            v_isSharedCheck_4098_ = (!lean_is_exclusive(v___x_4090_)) as u8;
                            if v_isSharedCheck_4098_ == 0 {
                                v___x_4093_ = v___x_4090_;
                                v_isShared_4094_ = v_isSharedCheck_4098_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4091_);
                                lean_dec(v___x_4090_);
                                v___x_4093_ = lean_box(0);
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
                    v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
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
                    v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
                    v___x_4096_ = v_reuseFailAlloc_4097_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4096_;
            }
            9 => {
                if lean_obj_tag(v_a_4100_) == 1 {
                    lean_dec_ref(v_pkgDir_4061_);
                    lean_dec_ref(v_name_4036_);
                    v_val_4101_ = lean_ctor_get(v_a_4100_, 0);
                    lean_inc_n(v_val_4101_, 2);
                    lean_dec_ref_known(v_a_4100_, 1);
                    v___x_4102_ = l_Lake_defaultManifestFile;
                    v___x_4103_ = l_Lake_joinRelative(v_val_4101_, v___x_4102_);
                    v___x_4104_ = lean_unsigned_to_nat(0);
                    v___x_4105_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_4106_ = l_Lake_Manifest_load(v___x_4103_);
                    if lean_obj_tag(v___x_4106_) == 0 {
                        v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
                        v_isSharedCheck_4114_ = (!lean_is_exclusive(v___x_4106_)) as u8;
                        if v_isSharedCheck_4114_ == 0 {
                            v___x_4109_ = v___x_4106_;
                            v_isShared_4110_ = v_isSharedCheck_4114_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4107_);
                            lean_dec(v___x_4106_);
                            v___x_4109_ = lean_box(0);
                            v_isShared_4110_ = v_isSharedCheck_4114_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_4115_ = lean_ctor_get(v___x_4106_, 0);
                        v_isSharedCheck_4122_ = (!lean_is_exclusive(v___x_4106_)) as u8;
                        if v_isSharedCheck_4122_ == 0 {
                            v___x_4117_ = v___x_4106_;
                            v_isShared_4118_ = v_isSharedCheck_4122_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_4115_);
                            lean_dec(v___x_4106_);
                            v___x_4117_ = lean_box(0);
                            v_isShared_4118_ = v_isSharedCheck_4122_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4100_);
                    lean_dec_ref(v_src_4039_);
                    lean_dec_ref(v_remoteUrl_4038_);
                    lean_dec_ref(v_relPkgDir_4037_);
                    lean_dec_ref(v_dep_4033_);
                    v___x_4123_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_4124_ = lean_string_append(v_name_4036_, v___x_4123_);
                    v___x_4125_ = lean_string_append(v___x_4124_, v_pkgDir_4061_);
                    lean_dec_ref(v_pkgDir_4061_);
                    v___x_4126_ = 3;
                    v___x_4127_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_4127_, 0, v___x_4125_);
                    lean_ctor_set_uint8(
                        v___x_4127_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_4126_,
                    );
                    lean_inc_ref(v_a_4040_);
                    v___x_4128_ = lean_apply_2(v_a_4040_, v___x_4127_, lean_box(0));
                    v___x_4129_ = lean_box(0);
                    v___x_4130_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4130_, 0, v___x_4129_);
                    return v___x_4130_;
                }
            }
            10 => {
                if v_isShared_4110_ == 0 {
                    lean_ctor_set_tag(v___x_4109_, 1);
                    v___x_4112_ = v___x_4109_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
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
                    lean_ctor_set_tag(v___x_4117_, 0);
                    v___x_4120_ = v___x_4117_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
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
                v___x_4135_ = lean_uint8_once(
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
                    v___x_4136_ = lean_box(0);
                    v___x_4137_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_4137_ == 0 {
                        if v___x_4135_ == 0 {
                            v_a_4100_ = v_val_4134_;
                            state = 9;
                            continue;
                        } else {
                            v___x_4138_ = 0usize;
                            v___x_4139_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_2450__overap_4140_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_4062_,
                                    v___f_4064_,
                                    v___x_4132_,
                                    v___x_4138_,
                                    v___x_4139_,
                                    v___x_4136_,
                                );
                            lean_inc_ref(v_a_4040_);
                            v___x_4141_ =
                                lean_apply_2(v___x_2450__overap_4140_, v_a_4040_, lean_box(0));
                            if lean_obj_tag(v___x_4141_) == 0 {
                                lean_dec_ref_known(v___x_4141_, 1);
                                v_a_4100_ = v_val_4134_;
                                state = 9;
                                continue;
                            } else {
                                lean_dec(v_val_4134_);
                                lean_dec_ref(v_pkgDir_4061_);
                                lean_dec_ref(v_src_4039_);
                                lean_dec_ref(v_remoteUrl_4038_);
                                lean_dec_ref(v_relPkgDir_4037_);
                                lean_dec_ref(v_name_4036_);
                                lean_dec_ref(v_dep_4033_);
                                v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
                                v_isSharedCheck_4149_ = (!lean_is_exclusive(v___x_4141_)) as u8;
                                if v_isSharedCheck_4149_ == 0 {
                                    v___x_4144_ = v___x_4141_;
                                    v_isShared_4145_ = v_isSharedCheck_4149_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_4142_);
                                    lean_dec(v___x_4141_);
                                    v___x_4144_ = lean_box(0);
                                    v_isShared_4145_ = v_isSharedCheck_4149_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4150_ = 0usize;
                        v___x_4151_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_2460__overap_4152_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_4062_,
                                v___f_4064_,
                                v___x_4132_,
                                v___x_4150_,
                                v___x_4151_,
                                v___x_4136_,
                            );
                        lean_inc_ref(v_a_4040_);
                        v___x_4153_ =
                            lean_apply_2(v___x_2460__overap_4152_, v_a_4040_, lean_box(0));
                        if lean_obj_tag(v___x_4153_) == 0 {
                            lean_dec_ref_known(v___x_4153_, 1);
                            v_a_4100_ = v_val_4134_;
                            state = 9;
                            continue;
                        } else {
                            lean_dec(v_val_4134_);
                            lean_dec_ref(v_pkgDir_4061_);
                            lean_dec_ref(v_src_4039_);
                            lean_dec_ref(v_remoteUrl_4038_);
                            lean_dec_ref(v_relPkgDir_4037_);
                            lean_dec_ref(v_name_4036_);
                            lean_dec_ref(v_dep_4033_);
                            v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
                            v_isSharedCheck_4161_ = (!lean_is_exclusive(v___x_4153_)) as u8;
                            if v_isSharedCheck_4161_ == 0 {
                                v___x_4156_ = v___x_4153_;
                                v_isShared_4157_ = v_isSharedCheck_4161_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_4154_);
                                lean_dec(v___x_4153_);
                                v___x_4156_ = lean_box(0);
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
                    v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
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
                    v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
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
    mut v_dep_4166_: *mut LeanObject,
    mut v_inherited_4167_: *mut LeanObject,
    mut v_wsDir_4168_: *mut LeanObject,
    mut v_name_4169_: *mut LeanObject,
    mut v_relPkgDir_4170_: *mut LeanObject,
    mut v_remoteUrl_4171_: *mut LeanObject,
    mut v_src_4172_: *mut LeanObject,
    mut v_a_4173_: *mut LeanObject,
    mut v_a_4174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inherited_boxed_4175_: u8 = 0;
    let mut v_res_4176_: *mut LeanObject = core::ptr::null_mut();
    v_inherited_boxed_4175_ = (lean_unbox(v_inherited_4167_) as u8);
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
    lean_dec_ref(v_a_4173_);
    return v_res_4176_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(
    mut v_a_4177_: *mut LeanObject,
    mut v_name_4178_: *mut LeanObject,
    mut v_repo_4179_: *mut LeanObject,
    mut v_url_4180_: *mut LeanObject,
    mut v_rev_x3f_4181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4183_: u8 = 0;
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: u8 = 0;
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: u8 = 0;
    let mut v___x_4191_: usize = 0;
    let mut v___x_4192_: usize = 0;
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: usize = 0;
    let mut v___x_4195_: usize = 0;
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4183_ = l_System_FilePath_isDir(v_repo_4179_);
                v___x_4187_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4188_ = lean_uint8_once(
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
                    v___x_4189_ = lean_box(0);
                    v___x_4190_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_4190_ == 0 {
                        if v___x_4188_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_4191_ = 0usize;
                            v___x_4192_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_4187_, v___x_4191_, v___x_4192_, v___x_4189_, v_a_4177_);
                            if lean_obj_tag(v___x_4193_) == 0 {
                                lean_dec_ref_known(v___x_4193_, 1);
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_rev_x3f_4181_);
                                lean_dec_ref(v_url_4180_);
                                lean_dec_ref(v_repo_4179_);
                                lean_dec_ref(v_name_4178_);
                                return v___x_4193_;
                            }
                        }
                    } else {
                        v___x_4194_ = 0usize;
                        v___x_4195_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_4187_, v___x_4194_, v___x_4195_, v___x_4189_, v_a_4177_);
                        if lean_obj_tag(v___x_4196_) == 0 {
                            lean_dec_ref_known(v___x_4196_, 1);
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_rev_x3f_4181_);
                            lean_dec_ref(v_url_4180_);
                            lean_dec_ref(v_repo_4179_);
                            lean_dec_ref(v_name_4178_);
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
    mut v_a_4197_: *mut LeanObject,
    mut v_name_4198_: *mut LeanObject,
    mut v_repo_4199_: *mut LeanObject,
    mut v_url_4200_: *mut LeanObject,
    mut v_rev_x3f_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4203_: *mut LeanObject = core::ptr::null_mut();
    v_res_4203_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_4197_, v_name_4198_, v_repo_4199_, v_url_4200_, v_rev_x3f_4201_);
    lean_dec_ref(v_a_4197_);
    return v_res_4203_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit(
    mut v_dep_4204_: *mut LeanObject,
    mut v_inherited_4205_: u8,
    mut v_lakeEnv_4206_: *mut LeanObject,
    mut v_wsDir_4207_: *mut LeanObject,
    mut v_name_4208_: *mut LeanObject,
    mut v_relPkgDir_4209_: *mut LeanObject,
    mut v_gitUrl_4210_: *mut LeanObject,
    mut v_remoteUrl_4211_: *mut LeanObject,
    mut v_inputRev_x3f_4212_: *mut LeanObject,
    mut v_subDir_x3f_4213_: *mut LeanObject,
    mut v_a_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___y_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: u8 = 0;
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    let mut v___x_4248_: usize = 0;
    let mut v___x_4249_: usize = 0;
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4254_: u8 = 0;
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4258_: u8 = 0;
    let mut v___x_4259_: usize = 0;
    let mut v___x_4260_: usize = 0;
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4265_: u8 = 0;
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4269_: u8 = 0;
    let mut v___y_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_a_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: u8 = 0;
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: usize = 0;
    let mut v___x_4317_: usize = 0;
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4322_: u8 = 0;
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut v___x_4327_: usize = 0;
    let mut v___x_4328_: usize = 0;
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut v___y_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: u8 = 0;
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gitDir_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: usize = 0;
    let mut v___x_4373_: usize = 0;
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4382_: u8 = 0;
    let mut v___x_4383_: usize = 0;
    let mut v___x_4384_: usize = 0;
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4389_: u8 = 0;
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v_a_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: u8 = 0;
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: usize = 0;
    let mut v___x_4404_: usize = 0;
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v___x_4414_: usize = 0;
    let mut v___x_4415_: usize = 0;
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4420_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4424_: u8 = 0;
    let mut v_isSharedCheck_4425_: u8 = 0;
    let mut v_unused_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4430_: u8 = 0;
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4434_: u8 = 0;
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut v_unused_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkgUrlMap_4219_ = lean_ctor_get(v_lakeEnv_4206_, 5);
                v_name_4220_ = lean_ctor_get(v_dep_4204_, 0);
                v_scope_4221_ = lean_ctor_get(v_dep_4204_, 1);
                v_isSharedCheck_4437_ = (!lean_is_exclusive(v_dep_4204_)) as u8;
                if v_isSharedCheck_4437_ == 0 {
                    v_unused_4438_ = lean_ctor_get(v_dep_4204_, 4);
                    lean_dec(v_unused_4438_);
                    v_unused_4439_ = lean_ctor_get(v_dep_4204_, 3);
                    lean_dec(v_unused_4439_);
                    v_unused_4440_ = lean_ctor_get(v_dep_4204_, 2);
                    lean_dec(v_unused_4440_);
                    v___x_4223_ = v_dep_4204_;
                    v_isShared_4224_ = v_isSharedCheck_4437_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_scope_4221_);
                    lean_inc(v_name_4220_);
                    lean_dec(v_dep_4204_);
                    v___x_4223_ = lean_box(0);
                    v_isShared_4224_ = v_isSharedCheck_4437_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4217_ = lean_box(0);
                v___x_4218_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4218_, 0, v___x_4217_);
                return v___x_4218_;
            }
            2 => {
                lean_inc_ref(v_relPkgDir_4209_);
                lean_inc_ref(v_wsDir_4207_);
                v_gitDir_4356_ = l_Lake_joinRelative(v_wsDir_4207_, v_relPkgDir_4209_);
                v___x_4435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_4219_, v_name_4220_);
                if lean_obj_tag(v___x_4435_) == 0 {
                    v___y_4358_ = v_gitUrl_4210_;
                    state = 22;
                    continue;
                } else {
                    lean_dec_ref(v_gitUrl_4210_);
                    v_val_4436_ = lean_ctor_get(v___x_4435_, 0);
                    lean_inc(v_val_4436_);
                    lean_dec_ref_known(v___x_4435_, 1);
                    v___y_4358_ = v_val_4436_;
                    state = 22;
                    continue;
                }
            }
            3 => {
                v___x_4230_ = l_Lake_defaultConfigFile;
                v___x_4231_ = lean_box(0);
                v___x_4232_ = lean_alloc_ctor(0, 5, (1) as u32);
                lean_ctor_set(v___x_4232_, 0, v_name_4220_);
                lean_ctor_set(v___x_4232_, 1, v_scope_4221_);
                lean_ctor_set(v___x_4232_, 2, v___x_4230_);
                lean_ctor_set(v___x_4232_, 3, v___x_4231_);
                lean_ctor_set(v___x_4232_, 4, v___y_4227_);
                lean_ctor_set_uint8(
                    v___x_4232_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v_inherited_4205_,
                );
                if v_isShared_4224_ == 0 {
                    lean_ctor_set(v___x_4223_, 4, v___x_4232_);
                    lean_ctor_set(v___x_4223_, 3, v_a_4229_);
                    lean_ctor_set(v___x_4223_, 2, v_remoteUrl_4211_);
                    lean_ctor_set(v___x_4223_, 1, v___y_4226_);
                    lean_ctor_set(v___x_4223_, 0, v___y_4228_);
                    v___x_4234_ = v___x_4223_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___y_4228_);
                    lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___y_4226_);
                    lean_ctor_set(v_reuseFailAlloc_4236_, 2, v_remoteUrl_4211_);
                    lean_ctor_set(v_reuseFailAlloc_4236_, 3, v_a_4229_);
                    lean_ctor_set(v_reuseFailAlloc_4236_, 4, v___x_4232_);
                    v___x_4234_ = v_reuseFailAlloc_4236_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4235_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4235_, 0, v___x_4234_);
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
                    v___x_4246_ = lean_box(0);
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
                            if lean_obj_tag(v___x_4250_) == 0 {
                                lean_dec_ref_known(v___x_4250_, 1);
                                v___y_4226_ = v___y_4239_;
                                v___y_4227_ = v___y_4238_;
                                v___y_4228_ = v___y_4241_;
                                v_a_4229_ = v_val_4243_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec_ref(v_val_4243_);
                                lean_dec_ref(v___y_4241_);
                                lean_dec_ref(v___y_4239_);
                                lean_dec_ref(v___y_4238_);
                                lean_del_object(v___x_4223_);
                                lean_dec_ref(v_scope_4221_);
                                lean_dec(v_name_4220_);
                                lean_dec_ref(v_remoteUrl_4211_);
                                v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
                                v_isSharedCheck_4258_ = (!lean_is_exclusive(v___x_4250_)) as u8;
                                if v_isSharedCheck_4258_ == 0 {
                                    v___x_4253_ = v___x_4250_;
                                    v_isShared_4254_ = v_isSharedCheck_4258_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_4251_);
                                    lean_dec(v___x_4250_);
                                    v___x_4253_ = lean_box(0);
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
                        if lean_obj_tag(v___x_4261_) == 0 {
                            lean_dec_ref_known(v___x_4261_, 1);
                            v___y_4226_ = v___y_4239_;
                            v___y_4227_ = v___y_4238_;
                            v___y_4228_ = v___y_4241_;
                            v_a_4229_ = v_val_4243_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec_ref(v_val_4243_);
                            lean_dec_ref(v___y_4241_);
                            lean_dec_ref(v___y_4239_);
                            lean_dec_ref(v___y_4238_);
                            lean_del_object(v___x_4223_);
                            lean_dec_ref(v_scope_4221_);
                            lean_dec(v_name_4220_);
                            lean_dec_ref(v_remoteUrl_4211_);
                            v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
                            v_isSharedCheck_4269_ = (!lean_is_exclusive(v___x_4261_)) as u8;
                            if v_isSharedCheck_4269_ == 0 {
                                v___x_4264_ = v___x_4261_;
                                v_isShared_4265_ = v_isSharedCheck_4269_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_4262_);
                                lean_dec(v___x_4261_);
                                v___x_4264_ = lean_box(0);
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
                    v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
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
                    v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
                    v___x_4267_ = v_reuseFailAlloc_4268_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4267_;
            }
            10 => {
                if lean_obj_tag(v_a_4274_) == 1 {
                    lean_dec_ref(v___y_4273_);
                    lean_dec_ref(v_name_4208_);
                    v_val_4275_ = lean_ctor_get(v_a_4274_, 0);
                    lean_inc_n(v_val_4275_, 2);
                    lean_dec_ref_known(v_a_4274_, 1);
                    v___x_4276_ = l_Lake_defaultManifestFile;
                    v___x_4277_ = l_Lake_joinRelative(v_val_4275_, v___x_4276_);
                    v___x_4278_ = lean_unsigned_to_nat(0);
                    v___x_4279_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_4280_ = l_Lake_Manifest_load(v___x_4277_);
                    if lean_obj_tag(v___x_4280_) == 0 {
                        v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
                        v_isSharedCheck_4288_ = (!lean_is_exclusive(v___x_4280_)) as u8;
                        if v_isSharedCheck_4288_ == 0 {
                            v___x_4283_ = v___x_4280_;
                            v_isShared_4284_ = v_isSharedCheck_4288_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4281_);
                            lean_dec(v___x_4280_);
                            v___x_4283_ = lean_box(0);
                            v_isShared_4284_ = v_isSharedCheck_4288_;
                            state = 11;
                            continue;
                        }
                    } else {
                        v_a_4289_ = lean_ctor_get(v___x_4280_, 0);
                        v_isSharedCheck_4296_ = (!lean_is_exclusive(v___x_4280_)) as u8;
                        if v_isSharedCheck_4296_ == 0 {
                            v___x_4291_ = v___x_4280_;
                            v_isShared_4292_ = v_isSharedCheck_4296_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4289_);
                            lean_dec(v___x_4280_);
                            v___x_4291_ = lean_box(0);
                            v_isShared_4292_ = v_isSharedCheck_4296_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4274_);
                    lean_dec_ref(v___y_4272_);
                    lean_dec_ref(v___y_4271_);
                    lean_del_object(v___x_4223_);
                    lean_dec_ref(v_scope_4221_);
                    lean_dec(v_name_4220_);
                    lean_dec_ref(v_remoteUrl_4211_);
                    v___x_4297_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_4298_ = lean_string_append(v_name_4208_, v___x_4297_);
                    v___x_4299_ = lean_string_append(v___x_4298_, v___y_4273_);
                    lean_dec_ref(v___y_4273_);
                    v___x_4300_ = 3;
                    v___x_4301_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_4301_, 0, v___x_4299_);
                    lean_ctor_set_uint8(
                        v___x_4301_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_4300_,
                    );
                    lean_inc_ref(v_a_4214_);
                    v___x_4302_ = lean_apply_2(v_a_4214_, v___x_4301_, lean_box(0));
                    v___x_4303_ = lean_box(0);
                    v___x_4304_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4304_, 0, v___x_4303_);
                    return v___x_4304_;
                }
            }
            11 => {
                if v_isShared_4284_ == 0 {
                    lean_ctor_set_tag(v___x_4283_, 1);
                    v___x_4286_ = v___x_4283_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
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
                    lean_ctor_set_tag(v___x_4291_, 0);
                    v___x_4294_ = v___x_4291_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
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
                    v___x_4314_ = lean_box(0);
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
                            if lean_obj_tag(v___x_4318_) == 0 {
                                lean_dec_ref_known(v___x_4318_, 1);
                                v___y_4271_ = v___y_4307_;
                                v___y_4272_ = v___y_4306_;
                                v___y_4273_ = v___y_4310_;
                                v_a_4274_ = v_val_4311_;
                                state = 10;
                                continue;
                            } else {
                                lean_dec(v_val_4311_);
                                lean_dec_ref(v___y_4310_);
                                lean_dec_ref(v___y_4307_);
                                lean_dec_ref(v___y_4306_);
                                lean_del_object(v___x_4223_);
                                lean_dec_ref(v_scope_4221_);
                                lean_dec(v_name_4220_);
                                lean_dec_ref(v_remoteUrl_4211_);
                                lean_dec_ref(v_name_4208_);
                                v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
                                v_isSharedCheck_4326_ = (!lean_is_exclusive(v___x_4318_)) as u8;
                                if v_isSharedCheck_4326_ == 0 {
                                    v___x_4321_ = v___x_4318_;
                                    v_isShared_4322_ = v_isSharedCheck_4326_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_4319_);
                                    lean_dec(v___x_4318_);
                                    v___x_4321_ = lean_box(0);
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
                        if lean_obj_tag(v___x_4329_) == 0 {
                            lean_dec_ref_known(v___x_4329_, 1);
                            v___y_4271_ = v___y_4307_;
                            v___y_4272_ = v___y_4306_;
                            v___y_4273_ = v___y_4310_;
                            v_a_4274_ = v_val_4311_;
                            state = 10;
                            continue;
                        } else {
                            lean_dec(v_val_4311_);
                            lean_dec_ref(v___y_4310_);
                            lean_dec_ref(v___y_4307_);
                            lean_dec_ref(v___y_4306_);
                            lean_del_object(v___x_4223_);
                            lean_dec_ref(v_scope_4221_);
                            lean_dec(v_name_4220_);
                            lean_dec_ref(v_remoteUrl_4211_);
                            lean_dec_ref(v_name_4208_);
                            v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
                            v_isSharedCheck_4337_ = (!lean_is_exclusive(v___x_4329_)) as u8;
                            if v_isSharedCheck_4337_ == 0 {
                                v___x_4332_ = v___x_4329_;
                                v_isShared_4333_ = v_isSharedCheck_4337_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4330_);
                                lean_dec(v___x_4329_);
                                v___x_4332_ = lean_box(0);
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
                    v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
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
                    v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
                    v___x_4335_ = v_reuseFailAlloc_4336_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4335_;
            }
            20 => {
                lean_inc_ref(v___y_4341_);
                v_pkgDir_4342_ = l_Lake_joinRelative(v_wsDir_4207_, v___y_4341_);
                lean_inc_ref(v_pkgDir_4342_);
                v___x_4343_ = l_Lake_resolvePath(v_pkgDir_4342_);
                v___x_4344_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_4344_, 0, v___y_4339_);
                lean_ctor_set(v___x_4344_, 1, v___y_4340_);
                lean_ctor_set(v___x_4344_, 2, v_inputRev_x3f_4212_);
                lean_ctor_set(v___x_4344_, 3, v_subDir_x3f_4213_);
                v___x_4345_ = lean_unsigned_to_nat(0);
                v___x_4346_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4347_ = lean_string_utf8_byte_size(v___x_4343_);
                v___x_4348_ = lean_nat_dec_eq(v___x_4347_, v___x_4345_);
                if v___x_4348_ == 0 {
                    v___x_4349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4349_, 0, v___x_4343_);
                    v___y_4306_ = v___y_4341_;
                    v___y_4307_ = v___x_4344_;
                    v___y_4308_ = v___x_4346_;
                    v___y_4309_ = v___x_4345_;
                    v___y_4310_ = v_pkgDir_4342_;
                    v_val_4311_ = v___x_4349_;
                    state = 15;
                    continue;
                } else {
                    lean_dec_ref(v___x_4343_);
                    v___x_4350_ = lean_box(0);
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
                if lean_obj_tag(v_subDir_x3f_4213_) == 1 {
                    v_val_4354_ = lean_ctor_get(v_subDir_x3f_4213_, 0);
                    lean_inc(v_val_4354_);
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
                lean_inc(v_inputRev_x3f_4212_);
                lean_inc_ref(v___y_4358_);
                lean_inc_ref(v_gitDir_4356_);
                lean_inc_ref(v_name_4208_);
                v___x_4359_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_4214_, v_name_4208_, v_gitDir_4356_, v___y_4358_, v_inputRev_x3f_4212_);
                if lean_obj_tag(v___x_4359_) == 0 {
                    v_isSharedCheck_4425_ = (!lean_is_exclusive(v___x_4359_)) as u8;
                    if v_isSharedCheck_4425_ == 0 {
                        v_unused_4426_ = lean_ctor_get(v___x_4359_, 0);
                        lean_dec(v_unused_4426_);
                        v___x_4361_ = v___x_4359_;
                        v_isShared_4362_ = v_isSharedCheck_4425_;
                        state = 23;
                        continue;
                    } else {
                        lean_dec(v___x_4359_);
                        v___x_4361_ = lean_box(0);
                        v_isShared_4362_ = v_isSharedCheck_4425_;
                        state = 23;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_4358_);
                    lean_dec_ref(v_gitDir_4356_);
                    lean_del_object(v___x_4223_);
                    lean_dec_ref(v_scope_4221_);
                    lean_dec(v_name_4220_);
                    lean_dec(v_subDir_x3f_4213_);
                    lean_dec(v_inputRev_x3f_4212_);
                    lean_dec_ref(v_remoteUrl_4211_);
                    lean_dec_ref(v_relPkgDir_4209_);
                    lean_dec_ref(v_name_4208_);
                    lean_dec_ref(v_wsDir_4207_);
                    v_a_4427_ = lean_ctor_get(v___x_4359_, 0);
                    v_isSharedCheck_4434_ = (!lean_is_exclusive(v___x_4359_)) as u8;
                    if v_isSharedCheck_4434_ == 0 {
                        v___x_4429_ = v___x_4359_;
                        v_isShared_4430_ = v_isSharedCheck_4434_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_4427_);
                        lean_dec(v___x_4359_);
                        v___x_4429_ = lean_box(0);
                        v_isShared_4430_ = v_isSharedCheck_4434_;
                        state = 33;
                        continue;
                    }
                }
            }
            23 => {
                v___x_4363_ = lean_unsigned_to_nat(0);
                v___x_4364_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4365_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_4356_, v___x_4364_);
                if lean_obj_tag(v___x_4365_) == 0 {
                    lean_del_object(v___x_4361_);
                    v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
                    lean_inc(v_a_4366_);
                    v_a_4367_ = lean_ctor_get(v___x_4365_, 1);
                    lean_inc(v_a_4367_);
                    lean_dec_ref_known(v___x_4365_, 2);
                    v___x_4368_ = lean_array_get_size(v_a_4367_);
                    v___x_4369_ = lean_nat_dec_lt(v___x_4363_, v___x_4368_);
                    if v___x_4369_ == 0 {
                        lean_dec(v_a_4367_);
                        v___y_4352_ = v___y_4358_;
                        v_a_4353_ = v_a_4366_;
                        state = 21;
                        continue;
                    } else {
                        v___x_4370_ = lean_box(0);
                        v___x_4371_ = lean_nat_dec_le(v___x_4368_, v___x_4368_);
                        if v___x_4371_ == 0 {
                            if v___x_4369_ == 0 {
                                lean_dec(v_a_4367_);
                                v___y_4352_ = v___y_4358_;
                                v_a_4353_ = v_a_4366_;
                                state = 21;
                                continue;
                            } else {
                                v___x_4372_ = 0usize;
                                v___x_4373_ = lean_usize_of_nat(v___x_4368_);
                                v___x_4374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4367_, v___x_4372_, v___x_4373_, v___x_4370_, v_a_4214_);
                                lean_dec(v_a_4367_);
                                if lean_obj_tag(v___x_4374_) == 0 {
                                    lean_dec_ref_known(v___x_4374_, 1);
                                    v___y_4352_ = v___y_4358_;
                                    v_a_4353_ = v_a_4366_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_dec(v_a_4366_);
                                    lean_dec_ref(v___y_4358_);
                                    lean_del_object(v___x_4223_);
                                    lean_dec_ref(v_scope_4221_);
                                    lean_dec(v_name_4220_);
                                    lean_dec(v_subDir_x3f_4213_);
                                    lean_dec(v_inputRev_x3f_4212_);
                                    lean_dec_ref(v_remoteUrl_4211_);
                                    lean_dec_ref(v_relPkgDir_4209_);
                                    lean_dec_ref(v_name_4208_);
                                    lean_dec_ref(v_wsDir_4207_);
                                    v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
                                    v_isSharedCheck_4382_ = (!lean_is_exclusive(v___x_4374_)) as u8;
                                    if v_isSharedCheck_4382_ == 0 {
                                        v___x_4377_ = v___x_4374_;
                                        v_isShared_4378_ = v_isSharedCheck_4382_;
                                        state = 24;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4375_);
                                        lean_dec(v___x_4374_);
                                        v___x_4377_ = lean_box(0);
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
                            lean_dec(v_a_4367_);
                            if lean_obj_tag(v___x_4385_) == 0 {
                                lean_dec_ref_known(v___x_4385_, 1);
                                v___y_4352_ = v___y_4358_;
                                v_a_4353_ = v_a_4366_;
                                state = 21;
                                continue;
                            } else {
                                lean_dec(v_a_4366_);
                                lean_dec_ref(v___y_4358_);
                                lean_del_object(v___x_4223_);
                                lean_dec_ref(v_scope_4221_);
                                lean_dec(v_name_4220_);
                                lean_dec(v_subDir_x3f_4213_);
                                lean_dec(v_inputRev_x3f_4212_);
                                lean_dec_ref(v_remoteUrl_4211_);
                                lean_dec_ref(v_relPkgDir_4209_);
                                lean_dec_ref(v_name_4208_);
                                lean_dec_ref(v_wsDir_4207_);
                                v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
                                v_isSharedCheck_4393_ = (!lean_is_exclusive(v___x_4385_)) as u8;
                                if v_isSharedCheck_4393_ == 0 {
                                    v___x_4388_ = v___x_4385_;
                                    v_isShared_4389_ = v_isSharedCheck_4393_;
                                    state = 26;
                                    continue;
                                } else {
                                    lean_inc(v_a_4386_);
                                    lean_dec(v___x_4385_);
                                    v___x_4388_ = lean_box(0);
                                    v_isShared_4389_ = v_isSharedCheck_4393_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_4358_);
                    lean_del_object(v___x_4223_);
                    lean_dec_ref(v_scope_4221_);
                    lean_dec(v_name_4220_);
                    lean_dec(v_subDir_x3f_4213_);
                    lean_dec(v_inputRev_x3f_4212_);
                    lean_dec_ref(v_remoteUrl_4211_);
                    lean_dec_ref(v_relPkgDir_4209_);
                    lean_dec_ref(v_name_4208_);
                    lean_dec_ref(v_wsDir_4207_);
                    v_a_4394_ = lean_ctor_get(v___x_4365_, 1);
                    lean_inc(v_a_4394_);
                    lean_dec_ref_known(v___x_4365_, 2);
                    v___x_4395_ = lean_array_get_size(v_a_4394_);
                    v___x_4396_ = lean_nat_dec_lt(v___x_4363_, v___x_4395_);
                    if v___x_4396_ == 0 {
                        lean_dec(v_a_4394_);
                        v___x_4397_ = lean_box(0);
                        if v_isShared_4362_ == 0 {
                            lean_ctor_set_tag(v___x_4361_, 1);
                            lean_ctor_set(v___x_4361_, 0, v___x_4397_);
                            v___x_4399_ = v___x_4361_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
                            v___x_4399_ = v_reuseFailAlloc_4400_;
                            state = 28;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4361_);
                        v___x_4401_ = lean_box(0);
                        v___x_4402_ = lean_nat_dec_le(v___x_4395_, v___x_4395_);
                        if v___x_4402_ == 0 {
                            if v___x_4396_ == 0 {
                                lean_dec(v_a_4394_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4403_ = 0usize;
                                v___x_4404_ = lean_usize_of_nat(v___x_4395_);
                                v___x_4405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4394_, v___x_4403_, v___x_4404_, v___x_4401_, v_a_4214_);
                                lean_dec(v_a_4394_);
                                if lean_obj_tag(v___x_4405_) == 0 {
                                    lean_dec_ref_known(v___x_4405_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
                                    v_isSharedCheck_4413_ = (!lean_is_exclusive(v___x_4405_)) as u8;
                                    if v_isSharedCheck_4413_ == 0 {
                                        v___x_4408_ = v___x_4405_;
                                        v_isShared_4409_ = v_isSharedCheck_4413_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4406_);
                                        lean_dec(v___x_4405_);
                                        v___x_4408_ = lean_box(0);
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
                            lean_dec(v_a_4394_);
                            if lean_obj_tag(v___x_4416_) == 0 {
                                lean_dec_ref_known(v___x_4416_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
                                v_isSharedCheck_4424_ = (!lean_is_exclusive(v___x_4416_)) as u8;
                                if v_isSharedCheck_4424_ == 0 {
                                    v___x_4419_ = v___x_4416_;
                                    v_isShared_4420_ = v_isSharedCheck_4424_;
                                    state = 31;
                                    continue;
                                } else {
                                    lean_inc(v_a_4417_);
                                    lean_dec(v___x_4416_);
                                    v___x_4419_ = lean_box(0);
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
                    v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
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
                    v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
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
                    v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
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
                    v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
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
                    v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
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
    mut v_dep_4441_: *mut LeanObject,
    mut v_inherited_4442_: *mut LeanObject,
    mut v_lakeEnv_4443_: *mut LeanObject,
    mut v_wsDir_4444_: *mut LeanObject,
    mut v_name_4445_: *mut LeanObject,
    mut v_relPkgDir_4446_: *mut LeanObject,
    mut v_gitUrl_4447_: *mut LeanObject,
    mut v_remoteUrl_4448_: *mut LeanObject,
    mut v_inputRev_x3f_4449_: *mut LeanObject,
    mut v_subDir_x3f_4450_: *mut LeanObject,
    mut v_a_4451_: *mut LeanObject,
    mut v_a_4452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inherited_boxed_4453_: u8 = 0;
    let mut v_res_4454_: *mut LeanObject = core::ptr::null_mut();
    v_inherited_boxed_4453_ = (lean_unbox(v_inherited_4442_) as u8);
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
    lean_dec_ref(v_a_4451_);
    lean_dec_ref(v_lakeEnv_4443_);
    return v_res_4454_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(
    mut v_a_4455_: *mut LeanObject,
    mut v_dep_4456_: *mut LeanObject,
    mut v_inherited_4457_: u8,
    mut v_lakeEnv_4458_: *mut LeanObject,
    mut v_wsDir_4459_: *mut LeanObject,
    mut v_name_4460_: *mut LeanObject,
    mut v_relPkgDir_4461_: *mut LeanObject,
    mut v_gitUrl_4462_: *mut LeanObject,
    mut v_remoteUrl_4463_: *mut LeanObject,
    mut v_inputRev_x3f_4464_: *mut LeanObject,
    mut v_subDir_x3f_4465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4475_: u8 = 0;
    let mut v___y_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v___x_4499_: usize = 0;
    let mut v___x_4500_: usize = 0;
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut v___x_4510_: usize = 0;
    let mut v___x_4511_: usize = 0;
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4516_: u8 = 0;
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4520_: u8 = 0;
    let mut v___y_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4539_: u8 = 0;
    let mut v_a_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: u8 = 0;
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: usize = 0;
    let mut v___x_4568_: usize = 0;
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4573_: u8 = 0;
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4577_: u8 = 0;
    let mut v___x_4578_: usize = 0;
    let mut v___x_4579_: usize = 0;
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4584_: u8 = 0;
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4588_: u8 = 0;
    let mut v___y_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gitDir_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4613_: u8 = 0;
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: u8 = 0;
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: u8 = 0;
    let mut v___x_4623_: usize = 0;
    let mut v___x_4624_: usize = 0;
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4629_: u8 = 0;
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4633_: u8 = 0;
    let mut v___x_4634_: usize = 0;
    let mut v___x_4635_: usize = 0;
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4640_: u8 = 0;
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4644_: u8 = 0;
    let mut v_a_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: u8 = 0;
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: usize = 0;
    let mut v___x_4655_: usize = 0;
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4660_: u8 = 0;
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v___x_4665_: usize = 0;
    let mut v___x_4666_: usize = 0;
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4671_: u8 = 0;
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut v_isSharedCheck_4676_: u8 = 0;
    let mut v_unused_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4685_: u8 = 0;
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4688_: u8 = 0;
    let mut v_unused_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkgUrlMap_4470_ = lean_ctor_get(v_lakeEnv_4458_, 5);
                v_name_4471_ = lean_ctor_get(v_dep_4456_, 0);
                v_scope_4472_ = lean_ctor_get(v_dep_4456_, 1);
                v_isSharedCheck_4688_ = (!lean_is_exclusive(v_dep_4456_)) as u8;
                if v_isSharedCheck_4688_ == 0 {
                    v_unused_4689_ = lean_ctor_get(v_dep_4456_, 4);
                    lean_dec(v_unused_4689_);
                    v_unused_4690_ = lean_ctor_get(v_dep_4456_, 3);
                    lean_dec(v_unused_4690_);
                    v_unused_4691_ = lean_ctor_get(v_dep_4456_, 2);
                    lean_dec(v_unused_4691_);
                    v___x_4474_ = v_dep_4456_;
                    v_isShared_4475_ = v_isSharedCheck_4688_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_scope_4472_);
                    lean_inc(v_name_4471_);
                    lean_dec(v_dep_4456_);
                    v___x_4474_ = lean_box(0);
                    v_isShared_4475_ = v_isSharedCheck_4688_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4468_ = lean_box(0);
                v___x_4469_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4469_, 0, v___x_4468_);
                return v___x_4469_;
            }
            2 => {
                lean_inc_ref(v_relPkgDir_4461_);
                lean_inc_ref(v_wsDir_4459_);
                v_gitDir_4607_ = l_Lake_joinRelative(v_wsDir_4459_, v_relPkgDir_4461_);
                v___x_4686_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_4470_, v_name_4471_);
                if lean_obj_tag(v___x_4686_) == 0 {
                    v___y_4609_ = v_gitUrl_4462_;
                    state = 22;
                    continue;
                } else {
                    lean_dec_ref(v_gitUrl_4462_);
                    v_val_4687_ = lean_ctor_get(v___x_4686_, 0);
                    lean_inc(v_val_4687_);
                    lean_dec_ref_known(v___x_4686_, 1);
                    v___y_4609_ = v_val_4687_;
                    state = 22;
                    continue;
                }
            }
            3 => {
                v___x_4481_ = l_Lake_defaultConfigFile;
                v___x_4482_ = lean_box(0);
                v___x_4483_ = lean_alloc_ctor(0, 5, (1) as u32);
                lean_ctor_set(v___x_4483_, 0, v_name_4471_);
                lean_ctor_set(v___x_4483_, 1, v_scope_4472_);
                lean_ctor_set(v___x_4483_, 2, v___x_4481_);
                lean_ctor_set(v___x_4483_, 3, v___x_4482_);
                lean_ctor_set(v___x_4483_, 4, v___y_4477_);
                lean_ctor_set_uint8(
                    v___x_4483_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v_inherited_4457_,
                );
                if v_isShared_4475_ == 0 {
                    lean_ctor_set(v___x_4474_, 4, v___x_4483_);
                    lean_ctor_set(v___x_4474_, 3, v_a_4480_);
                    lean_ctor_set(v___x_4474_, 2, v_remoteUrl_4463_);
                    lean_ctor_set(v___x_4474_, 1, v___y_4479_);
                    lean_ctor_set(v___x_4474_, 0, v___y_4478_);
                    v___x_4485_ = v___x_4474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___y_4478_);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 1, v___y_4479_);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 2, v_remoteUrl_4463_);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 3, v_a_4480_);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 4, v___x_4483_);
                    v___x_4485_ = v_reuseFailAlloc_4487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4486_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4486_, 0, v___x_4485_);
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
                    v___x_4497_ = lean_box(0);
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
                            if lean_obj_tag(v___x_4501_) == 0 {
                                lean_dec_ref_known(v___x_4501_, 1);
                                v___y_4477_ = v___y_4489_;
                                v___y_4478_ = v___y_4492_;
                                v___y_4479_ = v___y_4493_;
                                v_a_4480_ = v_val_4494_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec_ref(v_val_4494_);
                                lean_dec_ref(v___y_4493_);
                                lean_dec_ref(v___y_4492_);
                                lean_dec_ref(v___y_4489_);
                                lean_del_object(v___x_4474_);
                                lean_dec_ref(v_scope_4472_);
                                lean_dec(v_name_4471_);
                                lean_dec_ref(v_remoteUrl_4463_);
                                v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
                                v_isSharedCheck_4509_ = (!lean_is_exclusive(v___x_4501_)) as u8;
                                if v_isSharedCheck_4509_ == 0 {
                                    v___x_4504_ = v___x_4501_;
                                    v_isShared_4505_ = v_isSharedCheck_4509_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_4502_);
                                    lean_dec(v___x_4501_);
                                    v___x_4504_ = lean_box(0);
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
                        if lean_obj_tag(v___x_4512_) == 0 {
                            lean_dec_ref_known(v___x_4512_, 1);
                            v___y_4477_ = v___y_4489_;
                            v___y_4478_ = v___y_4492_;
                            v___y_4479_ = v___y_4493_;
                            v_a_4480_ = v_val_4494_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec_ref(v_val_4494_);
                            lean_dec_ref(v___y_4493_);
                            lean_dec_ref(v___y_4492_);
                            lean_dec_ref(v___y_4489_);
                            lean_del_object(v___x_4474_);
                            lean_dec_ref(v_scope_4472_);
                            lean_dec(v_name_4471_);
                            lean_dec_ref(v_remoteUrl_4463_);
                            v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
                            v_isSharedCheck_4520_ = (!lean_is_exclusive(v___x_4512_)) as u8;
                            if v_isSharedCheck_4520_ == 0 {
                                v___x_4515_ = v___x_4512_;
                                v_isShared_4516_ = v_isSharedCheck_4520_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_4513_);
                                lean_dec(v___x_4512_);
                                v___x_4515_ = lean_box(0);
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
                    v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
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
                    v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
                    v___x_4518_ = v_reuseFailAlloc_4519_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4518_;
            }
            10 => {
                if lean_obj_tag(v_a_4525_) == 1 {
                    lean_dec_ref(v___y_4523_);
                    lean_dec_ref(v_name_4460_);
                    v_val_4526_ = lean_ctor_get(v_a_4525_, 0);
                    lean_inc_n(v_val_4526_, 2);
                    lean_dec_ref_known(v_a_4525_, 1);
                    v___x_4527_ = l_Lake_defaultManifestFile;
                    v___x_4528_ = l_Lake_joinRelative(v_val_4526_, v___x_4527_);
                    v___x_4529_ = lean_unsigned_to_nat(0);
                    v___x_4530_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_4531_ = l_Lake_Manifest_load(v___x_4528_);
                    if lean_obj_tag(v___x_4531_) == 0 {
                        v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
                        v_isSharedCheck_4539_ = (!lean_is_exclusive(v___x_4531_)) as u8;
                        if v_isSharedCheck_4539_ == 0 {
                            v___x_4534_ = v___x_4531_;
                            v_isShared_4535_ = v_isSharedCheck_4539_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4532_);
                            lean_dec(v___x_4531_);
                            v___x_4534_ = lean_box(0);
                            v_isShared_4535_ = v_isSharedCheck_4539_;
                            state = 11;
                            continue;
                        }
                    } else {
                        v_a_4540_ = lean_ctor_get(v___x_4531_, 0);
                        v_isSharedCheck_4547_ = (!lean_is_exclusive(v___x_4531_)) as u8;
                        if v_isSharedCheck_4547_ == 0 {
                            v___x_4542_ = v___x_4531_;
                            v_isShared_4543_ = v_isSharedCheck_4547_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4540_);
                            lean_dec(v___x_4531_);
                            v___x_4542_ = lean_box(0);
                            v_isShared_4543_ = v_isSharedCheck_4547_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4525_);
                    lean_dec_ref(v___y_4524_);
                    lean_dec_ref(v___y_4522_);
                    lean_del_object(v___x_4474_);
                    lean_dec_ref(v_scope_4472_);
                    lean_dec(v_name_4471_);
                    lean_dec_ref(v_remoteUrl_4463_);
                    v___x_4548_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_4549_ = lean_string_append(v_name_4460_, v___x_4548_);
                    v___x_4550_ = lean_string_append(v___x_4549_, v___y_4523_);
                    lean_dec_ref(v___y_4523_);
                    v___x_4551_ = 3;
                    v___x_4552_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_4552_, 0, v___x_4550_);
                    lean_ctor_set_uint8(
                        v___x_4552_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_4551_,
                    );
                    lean_inc_ref(v_a_4455_);
                    v___x_4553_ = lean_apply_2(v_a_4455_, v___x_4552_, lean_box(0));
                    v___x_4554_ = lean_box(0);
                    v___x_4555_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4555_, 0, v___x_4554_);
                    return v___x_4555_;
                }
            }
            11 => {
                if v_isShared_4535_ == 0 {
                    lean_ctor_set_tag(v___x_4534_, 1);
                    v___x_4537_ = v___x_4534_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
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
                    lean_ctor_set_tag(v___x_4542_, 0);
                    v___x_4545_ = v___x_4542_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
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
                    v___x_4565_ = lean_box(0);
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
                            if lean_obj_tag(v___x_4569_) == 0 {
                                lean_dec_ref_known(v___x_4569_, 1);
                                v___y_4522_ = v___y_4557_;
                                v___y_4523_ = v___y_4558_;
                                v___y_4524_ = v___y_4560_;
                                v_a_4525_ = v_val_4562_;
                                state = 10;
                                continue;
                            } else {
                                lean_dec(v_val_4562_);
                                lean_dec_ref(v___y_4560_);
                                lean_dec_ref(v___y_4558_);
                                lean_dec_ref(v___y_4557_);
                                lean_del_object(v___x_4474_);
                                lean_dec_ref(v_scope_4472_);
                                lean_dec(v_name_4471_);
                                lean_dec_ref(v_remoteUrl_4463_);
                                lean_dec_ref(v_name_4460_);
                                v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
                                v_isSharedCheck_4577_ = (!lean_is_exclusive(v___x_4569_)) as u8;
                                if v_isSharedCheck_4577_ == 0 {
                                    v___x_4572_ = v___x_4569_;
                                    v_isShared_4573_ = v_isSharedCheck_4577_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_4570_);
                                    lean_dec(v___x_4569_);
                                    v___x_4572_ = lean_box(0);
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
                        if lean_obj_tag(v___x_4580_) == 0 {
                            lean_dec_ref_known(v___x_4580_, 1);
                            v___y_4522_ = v___y_4557_;
                            v___y_4523_ = v___y_4558_;
                            v___y_4524_ = v___y_4560_;
                            v_a_4525_ = v_val_4562_;
                            state = 10;
                            continue;
                        } else {
                            lean_dec(v_val_4562_);
                            lean_dec_ref(v___y_4560_);
                            lean_dec_ref(v___y_4558_);
                            lean_dec_ref(v___y_4557_);
                            lean_del_object(v___x_4474_);
                            lean_dec_ref(v_scope_4472_);
                            lean_dec(v_name_4471_);
                            lean_dec_ref(v_remoteUrl_4463_);
                            lean_dec_ref(v_name_4460_);
                            v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
                            v_isSharedCheck_4588_ = (!lean_is_exclusive(v___x_4580_)) as u8;
                            if v_isSharedCheck_4588_ == 0 {
                                v___x_4583_ = v___x_4580_;
                                v_isShared_4584_ = v_isSharedCheck_4588_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4581_);
                                lean_dec(v___x_4580_);
                                v___x_4583_ = lean_box(0);
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
                    v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
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
                    v_reuseFailAlloc_4587_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
                    v___x_4586_ = v_reuseFailAlloc_4587_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4586_;
            }
            20 => {
                lean_inc_ref(v___y_4592_);
                v_pkgDir_4593_ = l_Lake_joinRelative(v_wsDir_4459_, v___y_4592_);
                lean_inc_ref(v_pkgDir_4593_);
                v___x_4594_ = l_Lake_resolvePath(v_pkgDir_4593_);
                v___x_4595_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_4595_, 0, v___y_4591_);
                lean_ctor_set(v___x_4595_, 1, v___y_4590_);
                lean_ctor_set(v___x_4595_, 2, v_inputRev_x3f_4464_);
                lean_ctor_set(v___x_4595_, 3, v_subDir_x3f_4465_);
                v___x_4596_ = lean_unsigned_to_nat(0);
                v___x_4597_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4598_ = lean_string_utf8_byte_size(v___x_4594_);
                v___x_4599_ = lean_nat_dec_eq(v___x_4598_, v___x_4596_);
                if v___x_4599_ == 0 {
                    v___x_4600_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4600_, 0, v___x_4594_);
                    v___y_4557_ = v___x_4595_;
                    v___y_4558_ = v_pkgDir_4593_;
                    v___y_4559_ = v___x_4597_;
                    v___y_4560_ = v___y_4592_;
                    v___y_4561_ = v___x_4596_;
                    v_val_4562_ = v___x_4600_;
                    state = 15;
                    continue;
                } else {
                    lean_dec_ref(v___x_4594_);
                    v___x_4601_ = lean_box(0);
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
                if lean_obj_tag(v_subDir_x3f_4465_) == 1 {
                    v_val_4605_ = lean_ctor_get(v_subDir_x3f_4465_, 0);
                    lean_inc(v_val_4605_);
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
                lean_inc(v_inputRev_x3f_4464_);
                lean_inc_ref(v___y_4609_);
                lean_inc_ref(v_gitDir_4607_);
                lean_inc_ref(v_name_4460_);
                v___x_4610_ = l___private_Lake_Load_Materialize_0__Lake_materializeGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit_spec__0(v_a_4455_, v_name_4460_, v_gitDir_4607_, v___y_4609_, v_inputRev_x3f_4464_);
                if lean_obj_tag(v___x_4610_) == 0 {
                    v_isSharedCheck_4676_ = (!lean_is_exclusive(v___x_4610_)) as u8;
                    if v_isSharedCheck_4676_ == 0 {
                        v_unused_4677_ = lean_ctor_get(v___x_4610_, 0);
                        lean_dec(v_unused_4677_);
                        v___x_4612_ = v___x_4610_;
                        v_isShared_4613_ = v_isSharedCheck_4676_;
                        state = 23;
                        continue;
                    } else {
                        lean_dec(v___x_4610_);
                        v___x_4612_ = lean_box(0);
                        v_isShared_4613_ = v_isSharedCheck_4676_;
                        state = 23;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_4609_);
                    lean_dec_ref(v_gitDir_4607_);
                    lean_del_object(v___x_4474_);
                    lean_dec_ref(v_scope_4472_);
                    lean_dec(v_name_4471_);
                    lean_dec(v_subDir_x3f_4465_);
                    lean_dec(v_inputRev_x3f_4464_);
                    lean_dec_ref(v_remoteUrl_4463_);
                    lean_dec_ref(v_relPkgDir_4461_);
                    lean_dec_ref(v_name_4460_);
                    lean_dec_ref(v_wsDir_4459_);
                    v_a_4678_ = lean_ctor_get(v___x_4610_, 0);
                    v_isSharedCheck_4685_ = (!lean_is_exclusive(v___x_4610_)) as u8;
                    if v_isSharedCheck_4685_ == 0 {
                        v___x_4680_ = v___x_4610_;
                        v_isShared_4681_ = v_isSharedCheck_4685_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_4678_);
                        lean_dec(v___x_4610_);
                        v___x_4680_ = lean_box(0);
                        v_isShared_4681_ = v_isSharedCheck_4685_;
                        state = 33;
                        continue;
                    }
                }
            }
            23 => {
                v___x_4614_ = lean_unsigned_to_nat(0);
                v___x_4615_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_4616_ = l_Lake_GitRepo_getHeadRevision(v_gitDir_4607_, v___x_4615_);
                if lean_obj_tag(v___x_4616_) == 0 {
                    lean_del_object(v___x_4612_);
                    v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
                    lean_inc(v_a_4617_);
                    v_a_4618_ = lean_ctor_get(v___x_4616_, 1);
                    lean_inc(v_a_4618_);
                    lean_dec_ref_known(v___x_4616_, 2);
                    v___x_4619_ = lean_array_get_size(v_a_4618_);
                    v___x_4620_ = lean_nat_dec_lt(v___x_4614_, v___x_4619_);
                    if v___x_4620_ == 0 {
                        lean_dec(v_a_4618_);
                        v___y_4603_ = v___y_4609_;
                        v_a_4604_ = v_a_4617_;
                        state = 21;
                        continue;
                    } else {
                        v___x_4621_ = lean_box(0);
                        v___x_4622_ = lean_nat_dec_le(v___x_4619_, v___x_4619_);
                        if v___x_4622_ == 0 {
                            if v___x_4620_ == 0 {
                                lean_dec(v_a_4618_);
                                v___y_4603_ = v___y_4609_;
                                v_a_4604_ = v_a_4617_;
                                state = 21;
                                continue;
                            } else {
                                v___x_4623_ = 0usize;
                                v___x_4624_ = lean_usize_of_nat(v___x_4619_);
                                v___x_4625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4618_, v___x_4623_, v___x_4624_, v___x_4621_, v_a_4455_);
                                lean_dec(v_a_4618_);
                                if lean_obj_tag(v___x_4625_) == 0 {
                                    lean_dec_ref_known(v___x_4625_, 1);
                                    v___y_4603_ = v___y_4609_;
                                    v_a_4604_ = v_a_4617_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_dec(v_a_4617_);
                                    lean_dec_ref(v___y_4609_);
                                    lean_del_object(v___x_4474_);
                                    lean_dec_ref(v_scope_4472_);
                                    lean_dec(v_name_4471_);
                                    lean_dec(v_subDir_x3f_4465_);
                                    lean_dec(v_inputRev_x3f_4464_);
                                    lean_dec_ref(v_remoteUrl_4463_);
                                    lean_dec_ref(v_relPkgDir_4461_);
                                    lean_dec_ref(v_name_4460_);
                                    lean_dec_ref(v_wsDir_4459_);
                                    v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
                                    v_isSharedCheck_4633_ = (!lean_is_exclusive(v___x_4625_)) as u8;
                                    if v_isSharedCheck_4633_ == 0 {
                                        v___x_4628_ = v___x_4625_;
                                        v_isShared_4629_ = v_isSharedCheck_4633_;
                                        state = 24;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4626_);
                                        lean_dec(v___x_4625_);
                                        v___x_4628_ = lean_box(0);
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
                            lean_dec(v_a_4618_);
                            if lean_obj_tag(v___x_4636_) == 0 {
                                lean_dec_ref_known(v___x_4636_, 1);
                                v___y_4603_ = v___y_4609_;
                                v_a_4604_ = v_a_4617_;
                                state = 21;
                                continue;
                            } else {
                                lean_dec(v_a_4617_);
                                lean_dec_ref(v___y_4609_);
                                lean_del_object(v___x_4474_);
                                lean_dec_ref(v_scope_4472_);
                                lean_dec(v_name_4471_);
                                lean_dec(v_subDir_x3f_4465_);
                                lean_dec(v_inputRev_x3f_4464_);
                                lean_dec_ref(v_remoteUrl_4463_);
                                lean_dec_ref(v_relPkgDir_4461_);
                                lean_dec_ref(v_name_4460_);
                                lean_dec_ref(v_wsDir_4459_);
                                v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
                                v_isSharedCheck_4644_ = (!lean_is_exclusive(v___x_4636_)) as u8;
                                if v_isSharedCheck_4644_ == 0 {
                                    v___x_4639_ = v___x_4636_;
                                    v_isShared_4640_ = v_isSharedCheck_4644_;
                                    state = 26;
                                    continue;
                                } else {
                                    lean_inc(v_a_4637_);
                                    lean_dec(v___x_4636_);
                                    v___x_4639_ = lean_box(0);
                                    v_isShared_4640_ = v_isSharedCheck_4644_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_4609_);
                    lean_del_object(v___x_4474_);
                    lean_dec_ref(v_scope_4472_);
                    lean_dec(v_name_4471_);
                    lean_dec(v_subDir_x3f_4465_);
                    lean_dec(v_inputRev_x3f_4464_);
                    lean_dec_ref(v_remoteUrl_4463_);
                    lean_dec_ref(v_relPkgDir_4461_);
                    lean_dec_ref(v_name_4460_);
                    lean_dec_ref(v_wsDir_4459_);
                    v_a_4645_ = lean_ctor_get(v___x_4616_, 1);
                    lean_inc(v_a_4645_);
                    lean_dec_ref_known(v___x_4616_, 2);
                    v___x_4646_ = lean_array_get_size(v_a_4645_);
                    v___x_4647_ = lean_nat_dec_lt(v___x_4614_, v___x_4646_);
                    if v___x_4647_ == 0 {
                        lean_dec(v_a_4645_);
                        v___x_4648_ = lean_box(0);
                        if v_isShared_4613_ == 0 {
                            lean_ctor_set_tag(v___x_4612_, 1);
                            lean_ctor_set(v___x_4612_, 0, v___x_4648_);
                            v___x_4650_ = v___x_4612_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
                            v___x_4650_ = v_reuseFailAlloc_4651_;
                            state = 28;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4612_);
                        v___x_4652_ = lean_box(0);
                        v___x_4653_ = lean_nat_dec_le(v___x_4646_, v___x_4646_);
                        if v___x_4653_ == 0 {
                            if v___x_4647_ == 0 {
                                lean_dec(v_a_4645_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4654_ = 0usize;
                                v___x_4655_ = lean_usize_of_nat(v___x_4646_);
                                v___x_4656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_a_4645_, v___x_4654_, v___x_4655_, v___x_4652_, v_a_4455_);
                                lean_dec(v_a_4645_);
                                if lean_obj_tag(v___x_4656_) == 0 {
                                    lean_dec_ref_known(v___x_4656_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
                                    v_isSharedCheck_4664_ = (!lean_is_exclusive(v___x_4656_)) as u8;
                                    if v_isSharedCheck_4664_ == 0 {
                                        v___x_4659_ = v___x_4656_;
                                        v_isShared_4660_ = v_isSharedCheck_4664_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4657_);
                                        lean_dec(v___x_4656_);
                                        v___x_4659_ = lean_box(0);
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
                            lean_dec(v_a_4645_);
                            if lean_obj_tag(v___x_4667_) == 0 {
                                lean_dec_ref_known(v___x_4667_, 1);
                                state = 1;
                                continue;
                            } else {
                                v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
                                v_isSharedCheck_4675_ = (!lean_is_exclusive(v___x_4667_)) as u8;
                                if v_isSharedCheck_4675_ == 0 {
                                    v___x_4670_ = v___x_4667_;
                                    v_isShared_4671_ = v_isSharedCheck_4675_;
                                    state = 31;
                                    continue;
                                } else {
                                    lean_inc(v_a_4668_);
                                    lean_dec(v___x_4667_);
                                    v___x_4670_ = lean_box(0);
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
                    v_reuseFailAlloc_4632_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4632_, 0, v_a_4626_);
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
                    v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
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
                    v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
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
                    v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
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
                    v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
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
    mut v_a_4692_: *mut LeanObject,
    mut v_dep_4693_: *mut LeanObject,
    mut v_inherited_4694_: *mut LeanObject,
    mut v_lakeEnv_4695_: *mut LeanObject,
    mut v_wsDir_4696_: *mut LeanObject,
    mut v_name_4697_: *mut LeanObject,
    mut v_relPkgDir_4698_: *mut LeanObject,
    mut v_gitUrl_4699_: *mut LeanObject,
    mut v_remoteUrl_4700_: *mut LeanObject,
    mut v_inputRev_x3f_4701_: *mut LeanObject,
    mut v_subDir_x3f_4702_: *mut LeanObject,
    mut v_a_4703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inherited_boxed_4704_: u8 = 0;
    let mut v_res_4705_: *mut LeanObject = core::ptr::null_mut();
    v_inherited_boxed_4704_ = (lean_unbox(v_inherited_4694_) as u8);
    v_res_4705_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_4692_, v_dep_4693_, v_inherited_boxed_4704_, v_lakeEnv_4695_, v_wsDir_4696_, v_name_4697_, v_relPkgDir_4698_, v_gitUrl_4699_, v_remoteUrl_4700_, v_inputRev_x3f_4701_, v_subDir_x3f_4702_);
    lean_dec_ref(v_lakeEnv_4695_);
    lean_dec_ref(v_a_4692_);
    return v_res_4705_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    v___x_4707_ =
        l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0;
    v___x_4708_ = lean_string_utf8_byte_size(v___x_4707_);
    return v___x_4708_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(
    mut v_s_4709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    v___x_4710_ =
        l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__0;
    v___x_4711_ = lean_string_utf8_byte_size(v_s_4709_);
    v___x_4712_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1_once), _init_l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg___closed__1);
    v___x_4713_ = lean_nat_dec_le(v___x_4712_, v___x_4711_);
    if v___x_4713_ == 0 {
        let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_4709_);
        v___x_4714_ = lean_box(0);
        return v___x_4714_;
    } else {
        let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4716_: u8 = 0;
        v___x_4715_ = lean_unsigned_to_nat(0);
        v___x_4716_ = lean_string_memcmp(
            v_s_4709_,
            v___x_4710_,
            v___x_4715_,
            v___x_4715_,
            v___x_4712_,
        );
        if v___x_4716_ == 0 {
            let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_4709_);
            v___x_4717_ = lean_box(0);
            return v___x_4717_;
        } else {
            let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_s_4709_);
            v___x_4718_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4718_, 0, v_s_4709_);
            lean_ctor_set(v___x_4718_, 1, v___x_4715_);
            lean_ctor_set(v___x_4718_, 2, v___x_4711_);
            v___x_4719_ = l_String_Slice_pos_x21(v___x_4718_, v___x_4712_);
            lean_dec_ref_known(v___x_4718_, 3);
            v___x_4720_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4720_, 0, v_s_4709_);
            lean_ctor_set(v___x_4720_, 1, v___x_4719_);
            lean_ctor_set(v___x_4720_, 2, v___x_4711_);
            v___x_4721_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4721_, 0, v___x_4720_);
            return v___x_4721_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(
    mut v_s_4722_: *mut LeanObject,
    mut v_pat_4723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    v___x_4724_ =
        l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_s_4722_);
    return v___x_4724_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___boxed(
    mut v_s_4725_: *mut LeanObject,
    mut v_pat_4726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4727_: *mut LeanObject = core::ptr::null_mut();
    v_res_4727_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2(
        v_s_4725_,
        v_pat_4726_,
    );
    lean_dec_ref(v_pat_4726_);
    return v_res_4727_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(
    mut v_ver_4731_: *mut LeanObject,
    mut v_as_4732_: *mut LeanObject,
    mut v_sz_4733_: usize,
    mut v_i_4734_: usize,
    mut v_b_4735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4736_: u8 = 0;
    let mut v_a_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_version_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: u8 = 0;
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: usize = 0;
    let mut v___x_4743_: usize = 0;
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4736_ = lean_usize_dec_lt(v_i_4734_, v_sz_4733_);
                if v___x_4736_ == 0 {
                    lean_inc_ref(v_b_4735_);
                    return v_b_4735_;
                } else {
                    v_a_4737_ = lean_array_uget_borrowed(v_as_4732_, v_i_4734_);
                    v_version_4738_ = lean_ctor_get(v_a_4737_, 0);
                    v___x_4739_ = lean_box(0);
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
                        lean_inc(v_a_4737_);
                        v___x_4745_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4745_, 0, v_a_4737_);
                        v___x_4746_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4746_, 0, v___x_4745_);
                        v___x_4747_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4747_, 0, v___x_4746_);
                        lean_ctor_set(v___x_4747_, 1, v___x_4739_);
                        return v___x_4747_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___boxed(
    mut v_ver_4748_: *mut LeanObject,
    mut v_as_4749_: *mut LeanObject,
    mut v_sz_4750_: *mut LeanObject,
    mut v_i_4751_: *mut LeanObject,
    mut v_b_4752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4753_: usize = 0;
    let mut v_i_boxed_4754_: usize = 0;
    let mut v_res_4755_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4753_ = lean_unbox_usize(v_sz_4750_);
    lean_dec(v_sz_4750_);
    v_i_boxed_4754_ = lean_unbox_usize(v_i_4751_);
    lean_dec(v_i_4751_);
    v_res_4755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v_ver_4748_, v_as_4749_, v_sz_boxed_4753_, v_i_boxed_4754_, v_b_4752_);
    lean_dec_ref(v_b_4752_);
    lean_dec_ref(v_as_4749_);
    lean_dec_ref(v_ver_4748_);
    return v_res_4755_;
}
pub unsafe fn l_Lake_Dependency_materialize(
    mut v_dep_4766_: *mut LeanObject,
    mut v_inherited_4767_: u8,
    mut v_lakeEnv_4768_: *mut LeanObject,
    mut v_wsDir_4769_: *mut LeanObject,
    mut v_relPkgsDir_4770_: *mut LeanObject,
    mut v_relParentDir_4771_: *mut LeanObject,
    mut v_a_4772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fullName_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_x3f_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_src_x3f_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toString_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: u8 = 0;
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4853_: u8 = 0;
    let mut v_unused_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4857_: usize = 0;
    let mut v___x_4858_: usize = 0;
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_version_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revision_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: u8 = 0;
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4883_: u8 = 0;
    let mut v___x_4884_: u8 = 0;
    let mut v_sname_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v_dir_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4892_: u8 = 0;
    let mut v_relPkgDir_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: u8 = 0;
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: u8 = 0;
    let mut v___x_4918_: usize = 0;
    let mut v___x_4919_: usize = 0;
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4924_: u8 = 0;
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut v___x_4929_: usize = 0;
    let mut v___x_4930_: usize = 0;
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_a_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut v_a_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: u8 = 0;
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: u8 = 0;
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: u8 = 0;
    let mut v___x_4979_: usize = 0;
    let mut v___x_4980_: usize = 0;
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4985_: u8 = 0;
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4989_: u8 = 0;
    let mut v___x_4990_: usize = 0;
    let mut v___x_4991_: usize = 0;
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4996_: u8 = 0;
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: u8 = 0;
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_isSharedCheck_5009_: u8 = 0;
    let mut v_unused_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_url_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subDir_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: u8 = 0;
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: u8 = 0;
    let mut v___x_5042_: usize = 0;
    let mut v___x_5043_: usize = 0;
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5048_: u8 = 0;
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5052_: u8 = 0;
    let mut v___x_5053_: usize = 0;
    let mut v___x_5054_: usize = 0;
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5059_: u8 = 0;
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5063_: u8 = 0;
    let mut v___y_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: u8 = 0;
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5081_: u8 = 0;
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v_url_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_githubUrl_x3f_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defaultBranch_x3f_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subDir_x3f_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fullName_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: u8 = 0;
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: usize = 0;
    let mut v___x_5110_: usize = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5119_: u8 = 0;
    let mut v___x_5120_: usize = 0;
    let mut v___x_5121_: usize = 0;
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5126_: u8 = 0;
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5130_: u8 = 0;
    let mut v_val_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: u8 = 0;
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: usize = 0;
    let mut v___x_5136_: usize = 0;
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5141_: u8 = 0;
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5145_: u8 = 0;
    let mut v___x_5146_: usize = 0;
    let mut v___x_5147_: usize = 0;
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5152_: u8 = 0;
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut v_rev_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: u8 = 0;
    let mut v___x_5162_: usize = 0;
    let mut v___x_5163_: usize = 0;
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5168_: u8 = 0;
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut v___x_5173_: usize = 0;
    let mut v___x_5174_: usize = 0;
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5183_: u8 = 0;
    let mut v_ver_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut v_isSharedCheck_5198_: u8 = 0;
    let mut v___y_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: u8 = 0;
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: u8 = 0;
    let mut v___x_5208_: usize = 0;
    let mut v___x_5209_: usize = 0;
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5214_: u8 = 0;
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5218_: u8 = 0;
    let mut v___x_5219_: usize = 0;
    let mut v___x_5220_: usize = 0;
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5229_: u8 = 0;
    let mut v___x_5230_: u8 = 0;
    let mut v_a_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5247_: u8 = 0;
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5252_: u8 = 0;
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5257_: u8 = 0;
    let mut v___x_5258_: u8 = 0;
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5270_: u8 = 0;
    let mut v_a_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5274_: u8 = 0;
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5278_: u8 = 0;
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: u8 = 0;
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_4808_ = lean_ctor_get(v_dep_4766_, 0);
                v_scope_4809_ = lean_ctor_get(v_dep_4766_, 1);
                v_version_x3f_4810_ = lean_ctor_get(v_dep_4766_, 2);
                v_src_x3f_4811_ = lean_ctor_get(v_dep_4766_, 3);
                lean_inc(v_src_x3f_4811_);
                if lean_obj_tag(v_src_x3f_4811_) == 1 {
                    v_val_4880_ = lean_ctor_get(v_src_x3f_4811_, 0);
                    v_isSharedCheck_5025_ = (!lean_is_exclusive(v_src_x3f_4811_)) as u8;
                    if v_isSharedCheck_5025_ == 0 {
                        v___x_4882_ = v_src_x3f_4811_;
                        v_isShared_4883_ = v_isSharedCheck_5025_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_val_4880_);
                        lean_dec(v_src_x3f_4811_);
                        v___x_4882_ = lean_box(0);
                        v_isShared_4883_ = v_isSharedCheck_5025_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_src_x3f_4811_);
                    lean_dec_ref(v_relParentDir_4771_);
                    v___x_5026_ = lean_string_utf8_byte_size(v_scope_4809_);
                    v___x_5027_ = lean_unsigned_to_nat(0);
                    v___x_5230_ = lean_nat_dec_eq(v___x_5026_, v___x_5027_);
                    if v___x_5230_ == 0 {
                        if lean_obj_tag(v_version_x3f_4810_) == 1 {
                            v_val_5242_ = lean_ctor_get(v_version_x3f_4810_, 0);
                            lean_inc(v_val_5242_);
                            v___x_5243_ = l_String_dropPrefix_x3f___at___00Lake_Dependency_materialize_spec__2___redArg(v_val_5242_);
                            if lean_obj_tag(v___x_5243_) == 1 {
                                v_val_5244_ = lean_ctor_get(v___x_5243_, 0);
                                v_isSharedCheck_5252_ = (!lean_is_exclusive(v___x_5243_)) as u8;
                                if v_isSharedCheck_5252_ == 0 {
                                    v___x_5246_ = v___x_5243_;
                                    v_isShared_5247_ = v_isSharedCheck_5252_;
                                    state = 61;
                                    continue;
                                } else {
                                    lean_inc(v_val_5244_);
                                    lean_dec(v___x_5243_);
                                    v___x_5246_ = lean_box(0);
                                    v_isShared_5247_ = v_isSharedCheck_5252_;
                                    state = 61;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_5243_);
                                lean_inc(v_val_5242_);
                                v___x_5253_ = l_Lake_VerRange_parse(v_val_5242_);
                                if lean_obj_tag(v___x_5253_) == 0 {
                                    lean_inc(v_name_4808_);
                                    lean_dec_ref(v_relPkgsDir_4770_);
                                    lean_dec_ref(v_wsDir_4769_);
                                    lean_dec_ref(v_lakeEnv_4768_);
                                    lean_dec_ref(v_dep_4766_);
                                    v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
                                    v_isSharedCheck_5270_ = (!lean_is_exclusive(v___x_5253_)) as u8;
                                    if v_isSharedCheck_5270_ == 0 {
                                        v___x_5256_ = v___x_5253_;
                                        v_isShared_5257_ = v_isSharedCheck_5270_;
                                        state = 63;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5254_);
                                        lean_dec(v___x_5253_);
                                        v___x_5256_ = lean_box(0);
                                        v_isShared_5257_ = v_isSharedCheck_5270_;
                                        state = 63;
                                        continue;
                                    }
                                } else {
                                    v_a_5271_ = lean_ctor_get(v___x_5253_, 0);
                                    v_isSharedCheck_5278_ = (!lean_is_exclusive(v___x_5253_)) as u8;
                                    if v_isSharedCheck_5278_ == 0 {
                                        v___x_5273_ = v___x_5253_;
                                        v_isShared_5274_ = v_isSharedCheck_5278_;
                                        state = 65;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5271_);
                                        lean_dec(v___x_5253_);
                                        v___x_5273_ = lean_box(0);
                                        v_isShared_5274_ = v_isSharedCheck_5278_;
                                        state = 65;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_5279_ = lean_box(0);
                            v_a_5232_ = v___x_5279_;
                            state = 60;
                            continue;
                        }
                    } else {
                        lean_inc(v_name_4808_);
                        lean_dec_ref(v_relPkgsDir_4770_);
                        lean_dec_ref(v_wsDir_4769_);
                        lean_dec_ref(v_lakeEnv_4768_);
                        lean_dec_ref(v_dep_4766_);
                        v___x_5280_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_4808_,
                                v___x_5230_,
                            );
                        v___x_5281_ = l_Lake_Dependency_materialize___closed__9;
                        v___x_5282_ = lean_string_append(v___x_5280_, v___x_5281_);
                        v___x_5283_ = 3;
                        v___x_5284_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_5284_, 0, v___x_5282_);
                        lean_ctor_set_uint8(
                            v___x_5284_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_5283_,
                        );
                        lean_inc_ref(v_a_4772_);
                        v___x_5285_ = lean_apply_2(v_a_4772_, v___x_5284_, lean_box(0));
                        v___x_5286_ = lean_box(0);
                        v___x_5287_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5287_, 0, v___x_5286_);
                        return v___x_5287_;
                    }
                }
            }
            1 => {
                v___x_4775_ = lean_box(0);
                v___x_4776_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4776_, 0, v___x_4775_);
                return v___x_4776_;
            }
            2 => {
                v_fullName_4780_ = lean_ctor_get(v___y_4778_, 1);
                lean_inc_ref(v_fullName_4780_);
                lean_dec_ref(v___y_4778_);
                v___x_4781_ = l_Lake_Dependency_materialize___closed__0;
                v___x_4782_ = lean_string_append(v_fullName_4780_, v___x_4781_);
                v___x_4783_ = 3;
                v___x_4784_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4784_, 0, v___x_4782_);
                lean_ctor_set_uint8(
                    v___x_4784_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4783_,
                );
                lean_inc_ref(v___y_4779_);
                v___x_4785_ = lean_apply_2(v___y_4779_, v___x_4784_, lean_box(0));
                v___x_4786_ = lean_box(0);
                v___x_4787_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4787_, 0, v___x_4786_);
                return v___x_4787_;
            }
            3 => {
                v___x_4796_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4796_, 0, v___y_4789_);
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
                lean_dec_ref(v_lakeEnv_4768_);
                return v___x_4797_;
            }
            4 => {
                if lean_obj_tag(v___y_4799_) == 0 {
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
                    v_val_4807_ = lean_ctor_get(v___y_4799_, 0);
                    lean_inc(v_val_4807_);
                    lean_dec_ref_known(v___y_4799_, 1);
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
                v_toString_4815_ = lean_ctor_get(v___y_4814_, 0);
                lean_inc_ref(v_toString_4815_);
                lean_dec_ref(v___y_4814_);
                v___x_4816_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                v___x_4817_ = lean_string_append(v_scope_4809_, v___x_4816_);
                v___x_4818_ = lean_string_append(v___x_4817_, v___y_4813_);
                lean_dec_ref(v___y_4813_);
                v___x_4819_ = l_Lake_Dependency_materialize___closed__1;
                v___x_4820_ = lean_string_append(v___x_4818_, v___x_4819_);
                v___x_4821_ = lean_string_append(v___x_4820_, v_toString_4815_);
                lean_dec_ref(v_toString_4815_);
                v___x_4822_ = l_Lake_Dependency_materialize___closed__2;
                v___x_4823_ = lean_string_append(v___x_4821_, v___x_4822_);
                v___x_4824_ = 3;
                v___x_4825_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4825_, 0, v___x_4823_);
                lean_ctor_set_uint8(
                    v___x_4825_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4824_,
                );
                lean_inc_ref(v_a_4772_);
                v___x_4826_ = lean_apply_2(v_a_4772_, v___x_4825_, lean_box(0));
                v___x_4827_ = lean_box(0);
                v___x_4828_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4828_, 0, v___x_4827_);
                return v___x_4828_;
            }
            6 => {
                if lean_obj_tag(v_a_4837_) == 0 {
                    lean_inc_ref(v_scope_4809_);
                    lean_dec_ref(v___y_4836_);
                    lean_dec_ref(v___y_4835_);
                    lean_dec_ref(v___y_4834_);
                    lean_dec_ref(v___y_4833_);
                    lean_dec(v___y_4832_);
                    lean_dec(v___y_4831_);
                    lean_dec_ref(v_wsDir_4769_);
                    lean_dec_ref(v_lakeEnv_4768_);
                    lean_dec_ref(v_dep_4766_);
                    v_isSharedCheck_4853_ = (!lean_is_exclusive(v_a_4837_)) as u8;
                    if v_isSharedCheck_4853_ == 0 {
                        v_unused_4854_ = lean_ctor_get(v_a_4837_, 0);
                        lean_dec(v_unused_4854_);
                        v___x_4839_ = v_a_4837_;
                        v_isShared_4840_ = v_isSharedCheck_4853_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v_a_4837_);
                        v___x_4839_ = lean_box(0);
                        v_isShared_4840_ = v_isSharedCheck_4853_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_4855_ = lean_ctor_get(v_a_4837_, 0);
                    lean_inc(v_a_4855_);
                    lean_dec_ref_known(v_a_4837_, 1);
                    v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1___closed__0;
                    v_sz_4857_ = lean_array_size(v_a_4855_);
                    v___x_4858_ = 0usize;
                    v___x_4859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Dependency_materialize_spec__1(v___y_4836_, v_a_4855_, v_sz_4857_, v___x_4858_, v___x_4856_);
                    lean_dec(v_a_4855_);
                    v_fst_4860_ = lean_ctor_get(v___x_4859_, 0);
                    lean_inc(v_fst_4860_);
                    lean_dec_ref(v___x_4859_);
                    if lean_obj_tag(v_fst_4860_) == 0 {
                        lean_inc_ref(v_scope_4809_);
                        lean_dec_ref(v___y_4835_);
                        lean_dec_ref(v___y_4834_);
                        lean_dec_ref(v___y_4833_);
                        lean_dec(v___y_4832_);
                        lean_dec(v___y_4831_);
                        lean_dec_ref(v_wsDir_4769_);
                        lean_dec_ref(v_lakeEnv_4768_);
                        lean_dec_ref(v_dep_4766_);
                        v___y_4813_ = v___y_4830_;
                        v___y_4814_ = v___y_4836_;
                        state = 5;
                        continue;
                    } else {
                        v_val_4861_ = lean_ctor_get(v_fst_4860_, 0);
                        lean_inc(v_val_4861_);
                        lean_dec_ref_known(v_fst_4860_, 1);
                        if lean_obj_tag(v_val_4861_) == 1 {
                            lean_dec_ref(v___y_4836_);
                            v_val_4862_ = lean_ctor_get(v_val_4861_, 0);
                            lean_inc(v_val_4862_);
                            lean_dec_ref_known(v_val_4861_, 1);
                            v_version_4863_ = lean_ctor_get(v_val_4862_, 0);
                            lean_inc_ref(v_version_4863_);
                            v_revision_4864_ = lean_ctor_get(v_val_4862_, 1);
                            lean_inc_ref(v_revision_4864_);
                            lean_dec(v_val_4862_);
                            v___x_4865_ =
                                l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                            lean_inc_ref(v_scope_4809_);
                            v___x_4866_ = lean_string_append(v_scope_4809_, v___x_4865_);
                            v___x_4867_ = lean_string_append(v___x_4866_, v___y_4830_);
                            lean_dec_ref(v___y_4830_);
                            v___x_4868_ = l_Lake_Dependency_materialize___closed__4;
                            v___x_4869_ = lean_string_append(v___x_4867_, v___x_4868_);
                            v___x_4870_ = l_Lake_StdVer_toString(v_version_4863_);
                            v___x_4871_ = lean_string_append(v___x_4869_, v___x_4870_);
                            lean_dec_ref(v___x_4870_);
                            v___x_4872_ = l_Lake_Dependency_materialize___closed__5;
                            v___x_4873_ = lean_string_append(v___x_4871_, v___x_4872_);
                            v___x_4874_ = lean_string_append(v___x_4873_, v_revision_4864_);
                            v___x_4875_ = l_Lake_Dependency_materialize___closed__6;
                            v___x_4876_ = lean_string_append(v___x_4874_, v___x_4875_);
                            v___x_4877_ = 1;
                            v___x_4878_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_4878_, 0, v___x_4876_);
                            lean_ctor_set_uint8(
                                v___x_4878_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_4877_,
                            );
                            lean_inc_ref(v_a_4772_);
                            v___x_4879_ = lean_apply_2(v_a_4772_, v___x_4878_, lean_box(0));
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
                            lean_inc_ref(v_scope_4809_);
                            lean_dec(v_val_4861_);
                            lean_dec_ref(v___y_4835_);
                            lean_dec_ref(v___y_4834_);
                            lean_dec_ref(v___y_4833_);
                            lean_dec(v___y_4832_);
                            lean_dec(v___y_4831_);
                            lean_dec_ref(v_wsDir_4769_);
                            lean_dec_ref(v_lakeEnv_4768_);
                            lean_dec_ref(v_dep_4766_);
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
                lean_dec_ref(v___y_4830_);
                v___x_4844_ = l_Lake_Dependency_materialize___closed__3;
                v___x_4845_ = lean_string_append(v___x_4843_, v___x_4844_);
                v___x_4846_ = 3;
                v___x_4847_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4847_, 0, v___x_4845_);
                lean_ctor_set_uint8(
                    v___x_4847_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4846_,
                );
                lean_inc_ref(v_a_4772_);
                v___x_4848_ = lean_apply_2(v_a_4772_, v___x_4847_, lean_box(0));
                v___x_4849_ = lean_box(0);
                if v_isShared_4840_ == 0 {
                    lean_ctor_set_tag(v___x_4839_, 1);
                    lean_ctor_set(v___x_4839_, 0, v___x_4849_);
                    v___x_4851_ = v___x_4839_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
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
                lean_inc(v_name_4808_);
                v_sname_4885_ = l_Lean_Name_toString(v_name_4808_, v___x_4884_);
                if lean_obj_tag(v_val_4880_) == 0 {
                    lean_inc_ref(v_scope_4809_);
                    lean_inc(v_name_4808_);
                    lean_dec_ref(v_relPkgsDir_4770_);
                    lean_dec_ref(v_lakeEnv_4768_);
                    v_isSharedCheck_5009_ = (!lean_is_exclusive(v_dep_4766_)) as u8;
                    if v_isSharedCheck_5009_ == 0 {
                        v_unused_5010_ = lean_ctor_get(v_dep_4766_, 4);
                        lean_dec(v_unused_5010_);
                        v_unused_5011_ = lean_ctor_get(v_dep_4766_, 3);
                        lean_dec(v_unused_5011_);
                        v_unused_5012_ = lean_ctor_get(v_dep_4766_, 2);
                        lean_dec(v_unused_5012_);
                        v_unused_5013_ = lean_ctor_get(v_dep_4766_, 1);
                        lean_dec(v_unused_5013_);
                        v_unused_5014_ = lean_ctor_get(v_dep_4766_, 0);
                        lean_dec(v_unused_5014_);
                        v___x_4887_ = v_dep_4766_;
                        v_isShared_4888_ = v_isSharedCheck_5009_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec(v_dep_4766_);
                        v___x_4887_ = lean_box(0);
                        v_isShared_4888_ = v_isSharedCheck_5009_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4882_);
                    lean_dec_ref(v_relParentDir_4771_);
                    v_url_5015_ = lean_ctor_get(v_val_4880_, 0);
                    lean_inc_ref_n(v_url_5015_, 2);
                    v_rev_5016_ = lean_ctor_get(v_val_4880_, 1);
                    lean_inc(v_rev_5016_);
                    v_subDir_5017_ = lean_ctor_get(v_val_4880_, 2);
                    lean_inc(v_subDir_5017_);
                    lean_dec_ref_known(v_val_4880_, 3);
                    v___x_5022_ = l_Lake_Git_filterUrl_x3f(v_url_5015_);
                    if lean_obj_tag(v___x_5022_) == 0 {
                        v___x_5023_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                        v___y_5019_ = v___x_5023_;
                        state = 31;
                        continue;
                    } else {
                        v_val_5024_ = lean_ctor_get(v___x_5022_, 0);
                        lean_inc(v_val_5024_);
                        lean_dec_ref_known(v___x_5022_, 1);
                        v___y_5019_ = v_val_5024_;
                        state = 31;
                        continue;
                    }
                }
            }
            10 => {
                v_dir_4889_ = lean_ctor_get(v_val_4880_, 0);
                v_isSharedCheck_5008_ = (!lean_is_exclusive(v_val_4880_)) as u8;
                if v_isSharedCheck_5008_ == 0 {
                    v___x_4891_ = v_val_4880_;
                    v_isShared_4892_ = v_isSharedCheck_5008_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_dir_4889_);
                    lean_dec(v_val_4880_);
                    v___x_4891_ = lean_box(0);
                    v_isShared_4892_ = v_isSharedCheck_5008_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_relPkgDir_4893_ = l_Lake_joinRelative(v_relParentDir_4771_, v_dir_4889_);
                lean_inc_ref(v_relPkgDir_4893_);
                if v_isShared_4892_ == 0 {
                    lean_ctor_set(v___x_4891_, 0, v_relPkgDir_4893_);
                    v___x_4895_ = v___x_4891_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_relPkgDir_4893_);
                    v___x_4895_ = v_reuseFailAlloc_5007_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                lean_inc_ref(v_relPkgDir_4893_);
                v_pkgDir_4896_ = l_Lake_joinRelative(v_wsDir_4769_, v_relPkgDir_4893_);
                lean_inc_ref(v_pkgDir_4896_);
                v___x_4897_ = l_Lake_resolvePath(v_pkgDir_4896_);
                v___x_4898_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                v___x_4972_ = lean_unsigned_to_nat(0);
                v___x_4973_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_5001_ = lean_string_utf8_byte_size(v___x_4897_);
                v___x_5002_ = lean_nat_dec_eq(v___x_5001_, v___x_4972_);
                if v___x_5002_ == 0 {
                    if v_isShared_4883_ == 0 {
                        lean_ctor_set(v___x_4882_, 0, v___x_4897_);
                        v___x_5004_ = v___x_4882_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_4897_);
                        v___x_5004_ = v_reuseFailAlloc_5005_;
                        state = 30;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4897_);
                    lean_del_object(v___x_4882_);
                    v___x_5006_ = lean_box(0);
                    v_val_4975_ = v___x_5006_;
                    state = 25;
                    continue;
                }
            }
            13 => {
                v___x_4902_ = l_Lake_defaultConfigFile;
                v___x_4903_ = lean_box(0);
                v___x_4904_ = lean_alloc_ctor(0, 5, (1) as u32);
                lean_ctor_set(v___x_4904_, 0, v_name_4808_);
                lean_ctor_set(v___x_4904_, 1, v_scope_4809_);
                lean_ctor_set(v___x_4904_, 2, v___x_4902_);
                lean_ctor_set(v___x_4904_, 3, v___x_4903_);
                lean_ctor_set(v___x_4904_, 4, v___x_4895_);
                lean_ctor_set_uint8(
                    v___x_4904_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v_inherited_4767_,
                );
                if v_isShared_4888_ == 0 {
                    lean_ctor_set(v___x_4887_, 4, v___x_4904_);
                    lean_ctor_set(v___x_4887_, 3, v_a_4901_);
                    lean_ctor_set(v___x_4887_, 2, v___x_4898_);
                    lean_ctor_set(v___x_4887_, 1, v_relPkgDir_4893_);
                    lean_ctor_set(v___x_4887_, 0, v___y_4900_);
                    v___x_4906_ = v___x_4887_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___y_4900_);
                    lean_ctor_set(v_reuseFailAlloc_4908_, 1, v_relPkgDir_4893_);
                    lean_ctor_set(v_reuseFailAlloc_4908_, 2, v___x_4898_);
                    lean_ctor_set(v_reuseFailAlloc_4908_, 3, v_a_4901_);
                    lean_ctor_set(v_reuseFailAlloc_4908_, 4, v___x_4904_);
                    v___x_4906_ = v_reuseFailAlloc_4908_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4907_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4907_, 0, v___x_4906_);
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
                    v___x_4916_ = lean_box(0);
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
                            if lean_obj_tag(v___x_4920_) == 0 {
                                lean_dec_ref_known(v___x_4920_, 1);
                                v___y_4900_ = v___y_4912_;
                                v_a_4901_ = v_val_4913_;
                                state = 13;
                                continue;
                            } else {
                                lean_dec_ref(v_val_4913_);
                                lean_dec_ref(v___y_4912_);
                                lean_dec_ref(v___x_4895_);
                                lean_dec_ref(v_relPkgDir_4893_);
                                lean_del_object(v___x_4887_);
                                lean_dec_ref(v_scope_4809_);
                                lean_dec(v_name_4808_);
                                v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
                                v_isSharedCheck_4928_ = (!lean_is_exclusive(v___x_4920_)) as u8;
                                if v_isSharedCheck_4928_ == 0 {
                                    v___x_4923_ = v___x_4920_;
                                    v_isShared_4924_ = v_isSharedCheck_4928_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_4921_);
                                    lean_dec(v___x_4920_);
                                    v___x_4923_ = lean_box(0);
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
                        if lean_obj_tag(v___x_4931_) == 0 {
                            lean_dec_ref_known(v___x_4931_, 1);
                            v___y_4900_ = v___y_4912_;
                            v_a_4901_ = v_val_4913_;
                            state = 13;
                            continue;
                        } else {
                            lean_dec_ref(v_val_4913_);
                            lean_dec_ref(v___y_4912_);
                            lean_dec_ref(v___x_4895_);
                            lean_dec_ref(v_relPkgDir_4893_);
                            lean_del_object(v___x_4887_);
                            lean_dec_ref(v_scope_4809_);
                            lean_dec(v_name_4808_);
                            v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
                            v_isSharedCheck_4939_ = (!lean_is_exclusive(v___x_4931_)) as u8;
                            if v_isSharedCheck_4939_ == 0 {
                                v___x_4934_ = v___x_4931_;
                                v_isShared_4935_ = v_isSharedCheck_4939_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_4932_);
                                lean_dec(v___x_4931_);
                                v___x_4934_ = lean_box(0);
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
                    v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
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
                    v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
                    v___x_4937_ = v_reuseFailAlloc_4938_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4937_;
            }
            20 => {
                if lean_obj_tag(v_a_4941_) == 1 {
                    lean_dec_ref(v_pkgDir_4896_);
                    lean_dec_ref(v_sname_4885_);
                    v_val_4942_ = lean_ctor_get(v_a_4941_, 0);
                    lean_inc_n(v_val_4942_, 2);
                    lean_dec_ref_known(v_a_4941_, 1);
                    v___x_4943_ = l_Lake_defaultManifestFile;
                    v___x_4944_ = l_Lake_joinRelative(v_val_4942_, v___x_4943_);
                    v___x_4945_ = lean_unsigned_to_nat(0);
                    v___x_4946_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_4947_ = l_Lake_Manifest_load(v___x_4944_);
                    if lean_obj_tag(v___x_4947_) == 0 {
                        v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
                        v_isSharedCheck_4955_ = (!lean_is_exclusive(v___x_4947_)) as u8;
                        if v_isSharedCheck_4955_ == 0 {
                            v___x_4950_ = v___x_4947_;
                            v_isShared_4951_ = v_isSharedCheck_4955_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_4948_);
                            lean_dec(v___x_4947_);
                            v___x_4950_ = lean_box(0);
                            v_isShared_4951_ = v_isSharedCheck_4955_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v_a_4956_ = lean_ctor_get(v___x_4947_, 0);
                        v_isSharedCheck_4963_ = (!lean_is_exclusive(v___x_4947_)) as u8;
                        if v_isSharedCheck_4963_ == 0 {
                            v___x_4958_ = v___x_4947_;
                            v_isShared_4959_ = v_isSharedCheck_4963_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_4956_);
                            lean_dec(v___x_4947_);
                            v___x_4958_ = lean_box(0);
                            v_isShared_4959_ = v_isSharedCheck_4963_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4941_);
                    lean_dec_ref(v___x_4895_);
                    lean_dec_ref(v_relPkgDir_4893_);
                    lean_del_object(v___x_4887_);
                    lean_dec_ref(v_scope_4809_);
                    lean_dec(v_name_4808_);
                    v___x_4964_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_4965_ = lean_string_append(v_sname_4885_, v___x_4964_);
                    v___x_4966_ = lean_string_append(v___x_4965_, v_pkgDir_4896_);
                    lean_dec_ref(v_pkgDir_4896_);
                    v___x_4967_ = 3;
                    v___x_4968_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_4968_, 0, v___x_4966_);
                    lean_ctor_set_uint8(
                        v___x_4968_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_4967_,
                    );
                    lean_inc_ref(v_a_4772_);
                    v___x_4969_ = lean_apply_2(v_a_4772_, v___x_4968_, lean_box(0));
                    v___x_4970_ = lean_box(0);
                    v___x_4971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4971_, 0, v___x_4970_);
                    return v___x_4971_;
                }
            }
            21 => {
                if v_isShared_4951_ == 0 {
                    lean_ctor_set_tag(v___x_4950_, 1);
                    v___x_4953_ = v___x_4950_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
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
                    lean_ctor_set_tag(v___x_4958_, 0);
                    v___x_4961_ = v___x_4958_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
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
                v___x_4976_ = lean_uint8_once(
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
                    v___x_4977_ = lean_box(0);
                    v___x_4978_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_4978_ == 0 {
                        if v___x_4976_ == 0 {
                            v_a_4941_ = v_val_4975_;
                            state = 20;
                            continue;
                        } else {
                            v___x_4979_ = 0usize;
                            v___x_4980_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_4981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_4973_, v___x_4979_, v___x_4980_, v___x_4977_, v_a_4772_);
                            if lean_obj_tag(v___x_4981_) == 0 {
                                lean_dec_ref_known(v___x_4981_, 1);
                                v_a_4941_ = v_val_4975_;
                                state = 20;
                                continue;
                            } else {
                                lean_dec(v_val_4975_);
                                lean_dec_ref(v_pkgDir_4896_);
                                lean_dec_ref(v___x_4895_);
                                lean_dec_ref(v_relPkgDir_4893_);
                                lean_del_object(v___x_4887_);
                                lean_dec_ref(v_sname_4885_);
                                lean_dec_ref(v_scope_4809_);
                                lean_dec(v_name_4808_);
                                v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
                                v_isSharedCheck_4989_ = (!lean_is_exclusive(v___x_4981_)) as u8;
                                if v_isSharedCheck_4989_ == 0 {
                                    v___x_4984_ = v___x_4981_;
                                    v_isShared_4985_ = v_isSharedCheck_4989_;
                                    state = 26;
                                    continue;
                                } else {
                                    lean_inc(v_a_4982_);
                                    lean_dec(v___x_4981_);
                                    v___x_4984_ = lean_box(0);
                                    v_isShared_4985_ = v_isSharedCheck_4989_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4990_ = 0usize;
                        v___x_4991_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_4992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_4973_, v___x_4990_, v___x_4991_, v___x_4977_, v_a_4772_);
                        if lean_obj_tag(v___x_4992_) == 0 {
                            lean_dec_ref_known(v___x_4992_, 1);
                            v_a_4941_ = v_val_4975_;
                            state = 20;
                            continue;
                        } else {
                            lean_dec(v_val_4975_);
                            lean_dec_ref(v_pkgDir_4896_);
                            lean_dec_ref(v___x_4895_);
                            lean_dec_ref(v_relPkgDir_4893_);
                            lean_del_object(v___x_4887_);
                            lean_dec_ref(v_sname_4885_);
                            lean_dec_ref(v_scope_4809_);
                            lean_dec(v_name_4808_);
                            v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
                            v_isSharedCheck_5000_ = (!lean_is_exclusive(v___x_4992_)) as u8;
                            if v_isSharedCheck_5000_ == 0 {
                                v___x_4995_ = v___x_4992_;
                                v_isShared_4996_ = v_isSharedCheck_5000_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_4993_);
                                lean_dec(v___x_4992_);
                                v___x_4995_ = lean_box(0);
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
                    v_reuseFailAlloc_4988_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
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
                    v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
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
                lean_inc_ref(v_sname_4885_);
                v___x_5020_ = l_Lake_joinRelative(v_relPkgsDir_4770_, v_sname_4885_);
                v___x_5021_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_materializeGit___at___00Lake_Dependency_materialize_spec__0(v_a_4772_, v_dep_4766_, v_inherited_4767_, v_lakeEnv_4768_, v_wsDir_4769_, v_sname_4885_, v___x_5020_, v_url_5015_, v___y_5019_, v_rev_5016_, v_subDir_5017_);
                lean_dec_ref(v_lakeEnv_4768_);
                return v___x_5021_;
            }
            32 => {
                v___x_5038_ = lean_array_get_size(v_snd_5037_);
                v___x_5039_ = lean_nat_dec_lt(v___x_5027_, v___x_5038_);
                if v___x_5039_ == 0 {
                    lean_dec_ref(v_snd_5037_);
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
                    v___x_5040_ = lean_box(0);
                    v___x_5041_ = lean_nat_dec_le(v___x_5038_, v___x_5038_);
                    if v___x_5041_ == 0 {
                        if v___x_5039_ == 0 {
                            lean_dec_ref(v_snd_5037_);
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
                            lean_dec_ref(v_snd_5037_);
                            if lean_obj_tag(v___x_5044_) == 0 {
                                lean_dec_ref_known(v___x_5044_, 1);
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
                                lean_dec_ref(v_fst_5036_);
                                lean_dec_ref(v___y_5035_);
                                lean_dec_ref(v___y_5034_);
                                lean_dec_ref(v___y_5033_);
                                lean_dec_ref(v___y_5032_);
                                lean_dec(v___y_5031_);
                                lean_dec(v___y_5030_);
                                lean_dec_ref(v___y_5029_);
                                lean_dec_ref(v_wsDir_4769_);
                                lean_dec_ref(v_lakeEnv_4768_);
                                lean_dec_ref(v_dep_4766_);
                                v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
                                v_isSharedCheck_5052_ = (!lean_is_exclusive(v___x_5044_)) as u8;
                                if v_isSharedCheck_5052_ == 0 {
                                    v___x_5047_ = v___x_5044_;
                                    v_isShared_5048_ = v_isSharedCheck_5052_;
                                    state = 33;
                                    continue;
                                } else {
                                    lean_inc(v_a_5045_);
                                    lean_dec(v___x_5044_);
                                    v___x_5047_ = lean_box(0);
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
                        lean_dec_ref(v_snd_5037_);
                        if lean_obj_tag(v___x_5055_) == 0 {
                            lean_dec_ref_known(v___x_5055_, 1);
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
                            lean_dec_ref(v_fst_5036_);
                            lean_dec_ref(v___y_5035_);
                            lean_dec_ref(v___y_5034_);
                            lean_dec_ref(v___y_5033_);
                            lean_dec_ref(v___y_5032_);
                            lean_dec(v___y_5031_);
                            lean_dec(v___y_5030_);
                            lean_dec_ref(v___y_5029_);
                            lean_dec_ref(v_wsDir_4769_);
                            lean_dec_ref(v_lakeEnv_4768_);
                            lean_dec_ref(v_dep_4766_);
                            v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
                            v_isSharedCheck_5063_ = (!lean_is_exclusive(v___x_5055_)) as u8;
                            if v_isSharedCheck_5063_ == 0 {
                                v___x_5058_ = v___x_5055_;
                                v_isShared_5059_ = v_isSharedCheck_5063_;
                                state = 35;
                                continue;
                            } else {
                                lean_inc(v_a_5056_);
                                lean_dec(v___x_5055_);
                                v___x_5058_ = lean_box(0);
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
                    v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
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
                    v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
                    v___x_5061_ = v_reuseFailAlloc_5062_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5061_;
            }
            37 => {
                if lean_obj_tag(v_a_5067_) == 0 {
                    lean_inc_ref(v_scope_4809_);
                    lean_dec_ref_known(v_a_5067_, 1);
                    lean_dec(v___y_5066_);
                    lean_dec_ref(v_relPkgsDir_4770_);
                    lean_dec_ref(v_wsDir_4769_);
                    lean_dec_ref(v_lakeEnv_4768_);
                    lean_dec_ref(v_dep_4766_);
                    v___x_5068_ =
                        l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed___closed__0;
                    v___x_5069_ = lean_string_append(v_scope_4809_, v___x_5068_);
                    v___x_5070_ = lean_string_append(v___x_5069_, v___y_5065_);
                    lean_dec_ref(v___y_5065_);
                    v___x_5071_ = l_Lake_Dependency_materialize___closed__7;
                    v___x_5072_ = lean_string_append(v___x_5070_, v___x_5071_);
                    v___x_5073_ = 3;
                    v___x_5074_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_5074_, 0, v___x_5072_);
                    lean_ctor_set_uint8(
                        v___x_5074_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5073_,
                    );
                    lean_inc_ref(v_a_4772_);
                    v___x_5075_ = lean_apply_2(v_a_4772_, v___x_5074_, lean_box(0));
                    v___x_5076_ = lean_box(0);
                    v___x_5077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5077_, 0, v___x_5076_);
                    return v___x_5077_;
                } else {
                    v_a_5078_ = lean_ctor_get(v_a_5067_, 0);
                    v_isSharedCheck_5198_ = (!lean_is_exclusive(v_a_5067_)) as u8;
                    if v_isSharedCheck_5198_ == 0 {
                        v___x_5080_ = v_a_5067_;
                        v_isShared_5081_ = v_isSharedCheck_5198_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_a_5078_);
                        lean_dec(v_a_5067_);
                        v___x_5080_ = lean_box(0);
                        v_isShared_5081_ = v_isSharedCheck_5198_;
                        state = 38;
                        continue;
                    }
                }
            }
            38 => {
                if lean_obj_tag(v_a_5078_) == 0 {
                    lean_inc_ref(v_scope_4809_);
                    lean_del_object(v___x_5080_);
                    lean_dec_ref(v_relPkgsDir_4770_);
                    lean_dec_ref(v_wsDir_4769_);
                    lean_dec_ref(v_lakeEnv_4768_);
                    lean_dec_ref(v_dep_4766_);
                    v___x_5082_ = l___private_Lake_Load_Materialize_0__Lake_pkgNotIndexed(
                        v_scope_4809_,
                        v___y_5065_,
                        v___y_5066_,
                    );
                    lean_dec_ref(v___y_5065_);
                    v___x_5083_ = 3;
                    v___x_5084_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_5084_, 0, v___x_5082_);
                    lean_ctor_set_uint8(
                        v___x_5084_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5083_,
                    );
                    lean_inc_ref(v_a_4772_);
                    v___x_5085_ = lean_apply_2(v_a_4772_, v___x_5084_, lean_box(0));
                    v___x_5086_ = lean_box(0);
                    v___x_5087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5087_, 0, v___x_5086_);
                    return v___x_5087_;
                } else {
                    v_val_5088_ = lean_ctor_get(v_a_5078_, 0);
                    lean_inc(v_val_5088_);
                    lean_dec_ref_known(v_a_5078_, 1);
                    v___x_5089_ = l_Lake_RegistryPkg_gitSrc_x3f(v_val_5088_);
                    if lean_obj_tag(v___x_5089_) == 1 {
                        v_val_5090_ = lean_ctor_get(v___x_5089_, 0);
                        v_isSharedCheck_5197_ = (!lean_is_exclusive(v___x_5089_)) as u8;
                        if v_isSharedCheck_5197_ == 0 {
                            v___x_5092_ = v___x_5089_;
                            v_isShared_5093_ = v_isSharedCheck_5197_;
                            state = 39;
                            continue;
                        } else {
                            lean_inc(v_val_5090_);
                            lean_dec(v___x_5089_);
                            v___x_5092_ = lean_box(0);
                            v_isShared_5093_ = v_isSharedCheck_5197_;
                            state = 39;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5089_);
                        lean_del_object(v___x_5080_);
                        lean_dec(v___y_5066_);
                        lean_dec_ref(v___y_5065_);
                        lean_dec_ref(v_relPkgsDir_4770_);
                        lean_dec_ref(v_wsDir_4769_);
                        lean_dec_ref(v_lakeEnv_4768_);
                        lean_dec_ref(v_dep_4766_);
                        v___y_4778_ = v_val_5088_;
                        v___y_4779_ = v_a_4772_;
                        state = 2;
                        continue;
                    }
                }
            }
            39 => {
                if lean_obj_tag(v_val_5090_) == 0 {
                    v_url_5094_ = lean_ctor_get(v_val_5090_, 1);
                    lean_inc_ref(v_url_5094_);
                    v_githubUrl_x3f_5095_ = lean_ctor_get(v_val_5090_, 2);
                    lean_inc(v_githubUrl_x3f_5095_);
                    v_defaultBranch_x3f_5096_ = lean_ctor_get(v_val_5090_, 3);
                    lean_inc(v_defaultBranch_x3f_5096_);
                    v_subDir_x3f_5097_ = lean_ctor_get(v_val_5090_, 4);
                    lean_inc(v_subDir_x3f_5097_);
                    lean_dec_ref_known(v_val_5090_, 5);
                    v_name_5098_ = lean_ctor_get(v_val_5088_, 0);
                    lean_inc_ref(v_name_5098_);
                    v_fullName_5099_ = lean_ctor_get(v_val_5088_, 1);
                    lean_inc_ref(v_fullName_5099_);
                    lean_dec(v_val_5088_);
                    v___x_5100_ = l_Lake_joinRelative(v_relPkgsDir_4770_, v_name_5098_);
                    match lean_obj_tag(v___y_5066_) {
                        0 => {
                            lean_del_object(v___x_5080_);
                            lean_dec_ref(v___y_5065_);
                            v___x_5101_ =
                                l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                            if lean_obj_tag(v_defaultBranch_x3f_5096_) == 0 {
                                lean_dec_ref(v___x_5100_);
                                lean_dec_ref(v_fullName_5099_);
                                lean_dec(v_subDir_x3f_5097_);
                                lean_dec(v_githubUrl_x3f_5095_);
                                lean_dec_ref(v_url_5094_);
                                lean_dec_ref(v_wsDir_4769_);
                                lean_dec_ref(v_lakeEnv_4768_);
                                lean_dec_ref(v_dep_4766_);
                                v___x_5102_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
                                if v___x_5102_ == 0 {
                                    v___x_5103_ = lean_box(0);
                                    if v_isShared_5093_ == 0 {
                                        lean_ctor_set(v___x_5092_, 0, v___x_5103_);
                                        v___x_5105_ = v___x_5092_;
                                        state = 40;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___x_5103_);
                                        v___x_5105_ = v_reuseFailAlloc_5106_;
                                        state = 40;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_5092_);
                                    v___x_5107_ = lean_box(0);
                                    v___x_5108_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                                    if v___x_5108_ == 0 {
                                        if v___x_5102_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_5109_ = 0usize;
                                            v___x_5110_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                            v___x_5111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5101_, v___x_5109_, v___x_5110_, v___x_5107_, v_a_4772_);
                                            if lean_obj_tag(v___x_5111_) == 0 {
                                                lean_dec_ref_known(v___x_5111_, 1);
                                                state = 1;
                                                continue;
                                            } else {
                                                v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
                                                v_isSharedCheck_5119_ =
                                                    (!lean_is_exclusive(v___x_5111_)) as u8;
                                                if v_isSharedCheck_5119_ == 0 {
                                                    v___x_5114_ = v___x_5111_;
                                                    v_isShared_5115_ = v_isSharedCheck_5119_;
                                                    state = 41;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5112_);
                                                    lean_dec(v___x_5111_);
                                                    v___x_5114_ = lean_box(0);
                                                    v_isShared_5115_ = v_isSharedCheck_5119_;
                                                    state = 41;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_5120_ = 0usize;
                                        v___x_5121_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                        v___x_5122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5101_, v___x_5120_, v___x_5121_, v___x_5107_, v_a_4772_);
                                        if lean_obj_tag(v___x_5122_) == 0 {
                                            lean_dec_ref_known(v___x_5122_, 1);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
                                            v_isSharedCheck_5130_ =
                                                (!lean_is_exclusive(v___x_5122_)) as u8;
                                            if v_isSharedCheck_5130_ == 0 {
                                                v___x_5125_ = v___x_5122_;
                                                v_isShared_5126_ = v_isSharedCheck_5130_;
                                                state = 43;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5123_);
                                                lean_dec(v___x_5122_);
                                                v___x_5125_ = lean_box(0);
                                                v_isShared_5126_ = v_isSharedCheck_5130_;
                                                state = 43;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_del_object(v___x_5092_);
                                v_val_5131_ = lean_ctor_get(v_defaultBranch_x3f_5096_, 0);
                                lean_inc(v_val_5131_);
                                lean_dec_ref_known(v_defaultBranch_x3f_5096_, 1);
                                v___x_5132_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
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
                                    v___x_5133_ = lean_box(0);
                                    v___x_5134_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
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
                                            v___x_5136_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                            v___x_5137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5101_, v___x_5135_, v___x_5136_, v___x_5133_, v_a_4772_);
                                            if lean_obj_tag(v___x_5137_) == 0 {
                                                lean_dec_ref_known(v___x_5137_, 1);
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
                                                lean_dec(v_val_5131_);
                                                lean_dec_ref(v___x_5100_);
                                                lean_dec_ref(v_fullName_5099_);
                                                lean_dec(v_subDir_x3f_5097_);
                                                lean_dec(v_githubUrl_x3f_5095_);
                                                lean_dec_ref(v_url_5094_);
                                                lean_dec_ref(v_wsDir_4769_);
                                                lean_dec_ref(v_lakeEnv_4768_);
                                                lean_dec_ref(v_dep_4766_);
                                                v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
                                                v_isSharedCheck_5145_ =
                                                    (!lean_is_exclusive(v___x_5137_)) as u8;
                                                if v_isSharedCheck_5145_ == 0 {
                                                    v___x_5140_ = v___x_5137_;
                                                    v_isShared_5141_ = v_isSharedCheck_5145_;
                                                    state = 45;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5138_);
                                                    lean_dec(v___x_5137_);
                                                    v___x_5140_ = lean_box(0);
                                                    v_isShared_5141_ = v_isSharedCheck_5145_;
                                                    state = 45;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_5146_ = 0usize;
                                        v___x_5147_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                        v___x_5148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5101_, v___x_5146_, v___x_5147_, v___x_5133_, v_a_4772_);
                                        if lean_obj_tag(v___x_5148_) == 0 {
                                            lean_dec_ref_known(v___x_5148_, 1);
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
                                            lean_dec(v_val_5131_);
                                            lean_dec_ref(v___x_5100_);
                                            lean_dec_ref(v_fullName_5099_);
                                            lean_dec(v_subDir_x3f_5097_);
                                            lean_dec(v_githubUrl_x3f_5095_);
                                            lean_dec_ref(v_url_5094_);
                                            lean_dec_ref(v_wsDir_4769_);
                                            lean_dec_ref(v_lakeEnv_4768_);
                                            lean_dec_ref(v_dep_4766_);
                                            v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
                                            v_isSharedCheck_5156_ =
                                                (!lean_is_exclusive(v___x_5148_)) as u8;
                                            if v_isSharedCheck_5156_ == 0 {
                                                v___x_5151_ = v___x_5148_;
                                                v_isShared_5152_ = v_isSharedCheck_5156_;
                                                state = 47;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5149_);
                                                lean_dec(v___x_5148_);
                                                v___x_5151_ = lean_box(0);
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
                            lean_dec(v_defaultBranch_x3f_5096_);
                            lean_del_object(v___x_5092_);
                            lean_del_object(v___x_5080_);
                            lean_dec_ref(v___y_5065_);
                            v_rev_5157_ = lean_ctor_get(v___y_5066_, 0);
                            lean_inc_ref(v_rev_5157_);
                            lean_dec_ref_known(v___y_5066_, 1);
                            v___x_5158_ =
                                l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                            v___x_5159_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
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
                                v___x_5160_ = lean_box(0);
                                v___x_5161_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
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
                                        v___x_5163_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                        v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5158_, v___x_5162_, v___x_5163_, v___x_5160_, v_a_4772_);
                                        if lean_obj_tag(v___x_5164_) == 0 {
                                            lean_dec_ref_known(v___x_5164_, 1);
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
                                            lean_dec_ref(v_rev_5157_);
                                            lean_dec_ref(v___x_5100_);
                                            lean_dec_ref(v_fullName_5099_);
                                            lean_dec(v_subDir_x3f_5097_);
                                            lean_dec(v_githubUrl_x3f_5095_);
                                            lean_dec_ref(v_url_5094_);
                                            lean_dec_ref(v_wsDir_4769_);
                                            lean_dec_ref(v_lakeEnv_4768_);
                                            lean_dec_ref(v_dep_4766_);
                                            v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
                                            v_isSharedCheck_5172_ =
                                                (!lean_is_exclusive(v___x_5164_)) as u8;
                                            if v_isSharedCheck_5172_ == 0 {
                                                v___x_5167_ = v___x_5164_;
                                                v_isShared_5168_ = v_isSharedCheck_5172_;
                                                state = 49;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5165_);
                                                lean_dec(v___x_5164_);
                                                v___x_5167_ = lean_box(0);
                                                v_isShared_5168_ = v_isSharedCheck_5172_;
                                                state = 49;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    v___x_5173_ = 0usize;
                                    v___x_5174_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                    v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5158_, v___x_5173_, v___x_5174_, v___x_5160_, v_a_4772_);
                                    if lean_obj_tag(v___x_5175_) == 0 {
                                        lean_dec_ref_known(v___x_5175_, 1);
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
                                        lean_dec_ref(v_rev_5157_);
                                        lean_dec_ref(v___x_5100_);
                                        lean_dec_ref(v_fullName_5099_);
                                        lean_dec(v_subDir_x3f_5097_);
                                        lean_dec(v_githubUrl_x3f_5095_);
                                        lean_dec_ref(v_url_5094_);
                                        lean_dec_ref(v_wsDir_4769_);
                                        lean_dec_ref(v_lakeEnv_4768_);
                                        lean_dec_ref(v_dep_4766_);
                                        v_a_5176_ = lean_ctor_get(v___x_5175_, 0);
                                        v_isSharedCheck_5183_ =
                                            (!lean_is_exclusive(v___x_5175_)) as u8;
                                        if v_isSharedCheck_5183_ == 0 {
                                            v___x_5178_ = v___x_5175_;
                                            v_isShared_5179_ = v_isSharedCheck_5183_;
                                            state = 51;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5176_);
                                            lean_dec(v___x_5175_);
                                            v___x_5178_ = lean_box(0);
                                            v_isShared_5179_ = v_isSharedCheck_5183_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                        _ => {
                            lean_dec(v_defaultBranch_x3f_5096_);
                            lean_del_object(v___x_5092_);
                            v_ver_5184_ = lean_ctor_get(v___y_5066_, 0);
                            lean_inc_ref(v_ver_5184_);
                            lean_dec_ref_known(v___y_5066_, 1);
                            v___x_5185_ =
                                l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                            lean_inc_ref(v___y_5065_);
                            lean_inc_ref(v_scope_4809_);
                            lean_inc_ref(v_lakeEnv_4768_);
                            v___x_5186_ = l_Lake_Reservoir_fetchPkgVersions(
                                v_lakeEnv_4768_,
                                v_scope_4809_,
                                v___y_5065_,
                                v___x_5185_,
                            );
                            if lean_obj_tag(v___x_5186_) == 0 {
                                v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
                                lean_inc(v_a_5187_);
                                v_a_5188_ = lean_ctor_get(v___x_5186_, 1);
                                lean_inc(v_a_5188_);
                                lean_dec_ref_known(v___x_5186_, 2);
                                if v_isShared_5081_ == 0 {
                                    lean_ctor_set(v___x_5080_, 0, v_a_5187_);
                                    v___x_5190_ = v___x_5080_;
                                    state = 53;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5187_);
                                    v___x_5190_ = v_reuseFailAlloc_5191_;
                                    state = 53;
                                    continue;
                                }
                            } else {
                                v_a_5192_ = lean_ctor_get(v___x_5186_, 0);
                                lean_inc(v_a_5192_);
                                v_a_5193_ = lean_ctor_get(v___x_5186_, 1);
                                lean_inc(v_a_5193_);
                                lean_dec_ref_known(v___x_5186_, 2);
                                if v_isShared_5081_ == 0 {
                                    lean_ctor_set_tag(v___x_5080_, 0);
                                    lean_ctor_set(v___x_5080_, 0, v_a_5192_);
                                    v___x_5195_ = v___x_5080_;
                                    state = 54;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5196_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5192_);
                                    v___x_5195_ = v_reuseFailAlloc_5196_;
                                    state = 54;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5092_);
                    lean_dec(v_val_5090_);
                    lean_del_object(v___x_5080_);
                    lean_dec(v___y_5066_);
                    lean_dec_ref(v___y_5065_);
                    lean_dec_ref(v_relPkgsDir_4770_);
                    lean_dec_ref(v_wsDir_4769_);
                    lean_dec_ref(v_lakeEnv_4768_);
                    lean_dec_ref(v_dep_4766_);
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
                    v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
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
                    v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
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
                    v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
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
                    v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
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
                    v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
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
                    v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
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
                    lean_dec_ref(v_snd_5203_);
                    v___y_5065_ = v___y_5200_;
                    v___y_5066_ = v___y_5201_;
                    v_a_5067_ = v_fst_5202_;
                    state = 37;
                    continue;
                } else {
                    v___x_5206_ = lean_box(0);
                    v___x_5207_ = lean_nat_dec_le(v___x_5204_, v___x_5204_);
                    if v___x_5207_ == 0 {
                        if v___x_5205_ == 0 {
                            lean_dec_ref(v_snd_5203_);
                            v___y_5065_ = v___y_5200_;
                            v___y_5066_ = v___y_5201_;
                            v_a_5067_ = v_fst_5202_;
                            state = 37;
                            continue;
                        } else {
                            v___x_5208_ = 0usize;
                            v___x_5209_ = lean_usize_of_nat(v___x_5204_);
                            v___x_5210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v_snd_5203_, v___x_5208_, v___x_5209_, v___x_5206_, v_a_4772_);
                            lean_dec_ref(v_snd_5203_);
                            if lean_obj_tag(v___x_5210_) == 0 {
                                lean_dec_ref_known(v___x_5210_, 1);
                                v___y_5065_ = v___y_5200_;
                                v___y_5066_ = v___y_5201_;
                                v_a_5067_ = v_fst_5202_;
                                state = 37;
                                continue;
                            } else {
                                lean_dec_ref(v_fst_5202_);
                                lean_dec(v___y_5201_);
                                lean_dec_ref(v___y_5200_);
                                lean_dec_ref(v_relPkgsDir_4770_);
                                lean_dec_ref(v_wsDir_4769_);
                                lean_dec_ref(v_lakeEnv_4768_);
                                lean_dec_ref(v_dep_4766_);
                                v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
                                v_isSharedCheck_5218_ = (!lean_is_exclusive(v___x_5210_)) as u8;
                                if v_isSharedCheck_5218_ == 0 {
                                    v___x_5213_ = v___x_5210_;
                                    v_isShared_5214_ = v_isSharedCheck_5218_;
                                    state = 56;
                                    continue;
                                } else {
                                    lean_inc(v_a_5211_);
                                    lean_dec(v___x_5210_);
                                    v___x_5213_ = lean_box(0);
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
                        lean_dec_ref(v_snd_5203_);
                        if lean_obj_tag(v___x_5221_) == 0 {
                            lean_dec_ref_known(v___x_5221_, 1);
                            v___y_5065_ = v___y_5200_;
                            v___y_5066_ = v___y_5201_;
                            v_a_5067_ = v_fst_5202_;
                            state = 37;
                            continue;
                        } else {
                            lean_dec_ref(v_fst_5202_);
                            lean_dec(v___y_5201_);
                            lean_dec_ref(v___y_5200_);
                            lean_dec_ref(v_relPkgsDir_4770_);
                            lean_dec_ref(v_wsDir_4769_);
                            lean_dec_ref(v_lakeEnv_4768_);
                            lean_dec_ref(v_dep_4766_);
                            v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
                            v_isSharedCheck_5229_ = (!lean_is_exclusive(v___x_5221_)) as u8;
                            if v_isSharedCheck_5229_ == 0 {
                                v___x_5224_ = v___x_5221_;
                                v_isShared_5225_ = v_isSharedCheck_5229_;
                                state = 58;
                                continue;
                            } else {
                                lean_inc(v_a_5222_);
                                lean_dec(v___x_5221_);
                                v___x_5224_ = lean_box(0);
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
                    v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
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
                    v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
                    v___x_5227_ = v_reuseFailAlloc_5228_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_5227_;
            }
            60 => {
                lean_inc(v_name_4808_);
                v___x_5233_ = l_Lean_Name_toString(v_name_4808_, v___x_5230_);
                v___x_5234_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                lean_inc_ref(v___x_5233_);
                lean_inc_ref(v_scope_4809_);
                lean_inc_ref(v_lakeEnv_4768_);
                v___x_5235_ = l_Lake_Reservoir_fetchPkg_x3f(
                    v_lakeEnv_4768_,
                    v_scope_4809_,
                    v___x_5233_,
                    v___x_5234_,
                );
                if lean_obj_tag(v___x_5235_) == 0 {
                    v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
                    lean_inc(v_a_5236_);
                    v_a_5237_ = lean_ctor_get(v___x_5235_, 1);
                    lean_inc(v_a_5237_);
                    lean_dec_ref_known(v___x_5235_, 2);
                    v___x_5238_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5238_, 0, v_a_5236_);
                    v___y_5200_ = v___x_5233_;
                    v___y_5201_ = v_a_5232_;
                    v_fst_5202_ = v___x_5238_;
                    v_snd_5203_ = v_a_5237_;
                    state = 55;
                    continue;
                } else {
                    v_a_5239_ = lean_ctor_get(v___x_5235_, 0);
                    lean_inc(v_a_5239_);
                    v_a_5240_ = lean_ctor_get(v___x_5235_, 1);
                    lean_inc(v_a_5240_);
                    lean_dec_ref_known(v___x_5235_, 2);
                    v___x_5241_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5241_, 0, v_a_5239_);
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
                lean_dec(v_val_5244_);
                if v_isShared_5247_ == 0 {
                    lean_ctor_set(v___x_5246_, 0, v___x_5248_);
                    v___x_5250_ = v___x_5246_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5248_);
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
                lean_dec(v_a_5254_);
                v___x_5263_ = 3;
                v___x_5264_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_5264_, 0, v___x_5262_);
                lean_ctor_set_uint8(
                    v___x_5264_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5263_,
                );
                lean_inc_ref(v_a_4772_);
                v___x_5265_ = lean_apply_2(v_a_4772_, v___x_5264_, lean_box(0));
                v___x_5266_ = lean_box(0);
                if v_isShared_5257_ == 0 {
                    lean_ctor_set_tag(v___x_5256_, 1);
                    lean_ctor_set(v___x_5256_, 0, v___x_5266_);
                    v___x_5268_ = v___x_5256_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5266_);
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
                    lean_ctor_set_tag(v___x_5273_, 2);
                    v___x_5276_ = v___x_5273_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_5277_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5271_);
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
    mut v_dep_5288_: *mut LeanObject,
    mut v_inherited_5289_: *mut LeanObject,
    mut v_lakeEnv_5290_: *mut LeanObject,
    mut v_wsDir_5291_: *mut LeanObject,
    mut v_relPkgsDir_5292_: *mut LeanObject,
    mut v_relParentDir_5293_: *mut LeanObject,
    mut v_a_5294_: *mut LeanObject,
    mut v_a_5295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inherited_boxed_5296_: u8 = 0;
    let mut v_res_5297_: *mut LeanObject = core::ptr::null_mut();
    v_inherited_boxed_5296_ = (lean_unbox(v_inherited_5289_) as u8);
    v_res_5297_ = l_Lake_Dependency_materialize(
        v_dep_5288_,
        v_inherited_boxed_5296_,
        v_lakeEnv_5290_,
        v_wsDir_5291_,
        v_relPkgsDir_5292_,
        v_relParentDir_5293_,
        v_a_5294_,
    );
    lean_dec_ref(v_a_5294_);
    return v_res_5297_;
}
pub unsafe fn l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(
    mut v_manifestEntry_5303_: *mut LeanObject,
    mut v_wsDir_5304_: *mut LeanObject,
    mut v_relPkgDir_5305_: *mut LeanObject,
    mut v_remoteUrl_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: u8 = 0;
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: u8 = 0;
    let mut v___x_5328_: usize = 0;
    let mut v___x_5329_: usize = 0;
    let mut v___x_2400__overap_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5335_: u8 = 0;
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v___x_5340_: usize = 0;
    let mut v___x_5341_: usize = 0;
    let mut v___x_2410__overap_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5347_: u8 = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5351_: u8 = 0;
    let mut v_a_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut v_a_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5372_: u8 = 0;
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5376_: u8 = 0;
    let mut v_val_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: u8 = 0;
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: u8 = 0;
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: u8 = 0;
    let mut v___x_5397_: usize = 0;
    let mut v___x_5398_: usize = 0;
    let mut v___x_2466__overap_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v___x_5409_: usize = 0;
    let mut v___x_5410_: usize = 0;
    let mut v___x_2476__overap_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_relPkgDir_5305_);
                v_pkgDir_5314_ = l_Lake_joinRelative(v_wsDir_5304_, v_relPkgDir_5305_);
                v___x_5315_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1_once), _init_l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__1);
                lean_inc_ref(v_pkgDir_5314_);
                v___x_5316_ = l_Lake_resolvePath(v_pkgDir_5314_);
                v___f_5317_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__2;
                v___x_5390_ = lean_unsigned_to_nat(0);
                v___x_5391_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_5421_ = lean_string_utf8_byte_size(v___x_5316_);
                v___x_5422_ = lean_nat_dec_eq(v___x_5421_, v___x_5390_);
                if v___x_5422_ == 0 {
                    v___x_5423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5423_, 0, v___x_5316_);
                    v_val_5393_ = v___x_5423_;
                    state = 12;
                    continue;
                } else {
                    lean_dec_ref(v___x_5316_);
                    v___x_5424_ = lean_box(0);
                    v_val_5393_ = v___x_5424_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_5312_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5312_, 0, v___y_5310_);
                lean_ctor_set(v___x_5312_, 1, v_relPkgDir_5305_);
                lean_ctor_set(v___x_5312_, 2, v_remoteUrl_5306_);
                lean_ctor_set(v___x_5312_, 3, v_a_5311_);
                lean_ctor_set(v___x_5312_, 4, v_manifestEntry_5303_);
                v___x_5313_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5313_, 0, v___x_5312_);
                return v___x_5313_;
            }
            2 => {
                v___x_5324_ = lean_array_get_size(v___y_5320_);
                v___x_5325_ = lean_nat_dec_lt(v___y_5319_, v___x_5324_);
                if v___x_5325_ == 0 {
                    lean_dec_ref(v___y_5322_);
                    v___y_5310_ = v___y_5321_;
                    v_a_5311_ = v_val_5323_;
                    state = 1;
                    continue;
                } else {
                    v___x_5326_ = lean_box(0);
                    v___x_5327_ = lean_nat_dec_le(v___x_5324_, v___x_5324_);
                    if v___x_5327_ == 0 {
                        if v___x_5325_ == 0 {
                            lean_dec_ref(v___y_5322_);
                            v___y_5310_ = v___y_5321_;
                            v_a_5311_ = v_val_5323_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5328_ = 0usize;
                            v___x_5329_ = lean_usize_of_nat(v___x_5324_);
                            lean_inc_ref(v___y_5320_);
                            v___x_2400__overap_5330_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___y_5322_,
                                    v___f_5317_,
                                    v___y_5320_,
                                    v___x_5328_,
                                    v___x_5329_,
                                    v___x_5326_,
                                );
                            lean_inc_ref(v_a_5307_);
                            v___x_5331_ =
                                lean_apply_2(v___x_2400__overap_5330_, v_a_5307_, lean_box(0));
                            if lean_obj_tag(v___x_5331_) == 0 {
                                lean_dec_ref_known(v___x_5331_, 1);
                                v___y_5310_ = v___y_5321_;
                                v_a_5311_ = v_val_5323_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_val_5323_);
                                lean_dec_ref(v___y_5321_);
                                lean_dec_ref(v_remoteUrl_5306_);
                                lean_dec_ref(v_relPkgDir_5305_);
                                lean_dec_ref(v_manifestEntry_5303_);
                                v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
                                v_isSharedCheck_5339_ = (!lean_is_exclusive(v___x_5331_)) as u8;
                                if v_isSharedCheck_5339_ == 0 {
                                    v___x_5334_ = v___x_5331_;
                                    v_isShared_5335_ = v_isSharedCheck_5339_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_5332_);
                                    lean_dec(v___x_5331_);
                                    v___x_5334_ = lean_box(0);
                                    v_isShared_5335_ = v_isSharedCheck_5339_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5340_ = 0usize;
                        v___x_5341_ = lean_usize_of_nat(v___x_5324_);
                        lean_inc_ref(v___y_5320_);
                        v___x_2410__overap_5342_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___y_5322_,
                                v___f_5317_,
                                v___y_5320_,
                                v___x_5340_,
                                v___x_5341_,
                                v___x_5326_,
                            );
                        lean_inc_ref(v_a_5307_);
                        v___x_5343_ =
                            lean_apply_2(v___x_2410__overap_5342_, v_a_5307_, lean_box(0));
                        if lean_obj_tag(v___x_5343_) == 0 {
                            lean_dec_ref_known(v___x_5343_, 1);
                            v___y_5310_ = v___y_5321_;
                            v_a_5311_ = v_val_5323_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_val_5323_);
                            lean_dec_ref(v___y_5321_);
                            lean_dec_ref(v_remoteUrl_5306_);
                            lean_dec_ref(v_relPkgDir_5305_);
                            lean_dec_ref(v_manifestEntry_5303_);
                            v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
                            v_isSharedCheck_5351_ = (!lean_is_exclusive(v___x_5343_)) as u8;
                            if v_isSharedCheck_5351_ == 0 {
                                v___x_5346_ = v___x_5343_;
                                v_isShared_5347_ = v_isSharedCheck_5351_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5344_);
                                lean_dec(v___x_5343_);
                                v___x_5346_ = lean_box(0);
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
                    v_reuseFailAlloc_5338_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5332_);
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
                    v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
                    v___x_5349_ = v_reuseFailAlloc_5350_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5349_;
            }
            7 => {
                if lean_obj_tag(v_a_5353_) == 1 {
                    lean_dec_ref(v_pkgDir_5314_);
                    v_manifestFile_x3f_5354_ = lean_ctor_get(v_manifestEntry_5303_, 3);
                    if lean_obj_tag(v_manifestFile_x3f_5354_) == 1 {
                        v_val_5355_ = lean_ctor_get(v_a_5353_, 0);
                        lean_inc_n(v_val_5355_, 2);
                        lean_dec_ref_known(v_a_5353_, 1);
                        v_val_5356_ = lean_ctor_get(v_manifestFile_x3f_5354_, 0);
                        lean_inc(v_val_5356_);
                        v___x_5357_ = l_Lake_joinRelative(v_val_5355_, v_val_5356_);
                        v___x_5358_ = lean_unsigned_to_nat(0);
                        v___x_5359_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                        v___x_5360_ = l_Lake_Manifest_load(v___x_5357_);
                        if lean_obj_tag(v___x_5360_) == 0 {
                            v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
                            v_isSharedCheck_5368_ = (!lean_is_exclusive(v___x_5360_)) as u8;
                            if v_isSharedCheck_5368_ == 0 {
                                v___x_5363_ = v___x_5360_;
                                v_isShared_5364_ = v_isSharedCheck_5368_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_5361_);
                                lean_dec(v___x_5360_);
                                v___x_5363_ = lean_box(0);
                                v_isShared_5364_ = v_isSharedCheck_5368_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_5369_ = lean_ctor_get(v___x_5360_, 0);
                            v_isSharedCheck_5376_ = (!lean_is_exclusive(v___x_5360_)) as u8;
                            if v_isSharedCheck_5376_ == 0 {
                                v___x_5371_ = v___x_5360_;
                                v_isShared_5372_ = v_isSharedCheck_5376_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_5369_);
                                lean_dec(v___x_5360_);
                                v___x_5371_ = lean_box(0);
                                v_isShared_5372_ = v_isSharedCheck_5376_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_val_5377_ = lean_ctor_get(v_a_5353_, 0);
                        lean_inc(v_val_5377_);
                        lean_dec_ref_known(v_a_5353_, 1);
                        v___x_5378_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1;
                        v___y_5310_ = v_val_5377_;
                        v_a_5311_ = v___x_5378_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5353_);
                    lean_dec_ref(v_remoteUrl_5306_);
                    lean_dec_ref(v_relPkgDir_5305_);
                    v_name_5379_ = lean_ctor_get(v_manifestEntry_5303_, 0);
                    lean_inc(v_name_5379_);
                    lean_dec_ref(v_manifestEntry_5303_);
                    v___x_5380_ = 0;
                    v___x_5381_ = l_Lean_Name_toString(v_name_5379_, v___x_5380_);
                    v___x_5382_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_5383_ = lean_string_append(v___x_5381_, v___x_5382_);
                    v___x_5384_ = lean_string_append(v___x_5383_, v_pkgDir_5314_);
                    lean_dec_ref(v_pkgDir_5314_);
                    v___x_5385_ = 3;
                    v___x_5386_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_5386_, 0, v___x_5384_);
                    lean_ctor_set_uint8(
                        v___x_5386_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5385_,
                    );
                    lean_inc_ref(v_a_5307_);
                    v___x_5387_ = lean_apply_2(v_a_5307_, v___x_5386_, lean_box(0));
                    v___x_5388_ = lean_box(0);
                    v___x_5389_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5389_, 0, v___x_5388_);
                    return v___x_5389_;
                }
            }
            8 => {
                if v_isShared_5364_ == 0 {
                    lean_ctor_set_tag(v___x_5363_, 1);
                    v___x_5366_ = v___x_5363_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
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
                    lean_ctor_set_tag(v___x_5371_, 0);
                    v___x_5374_ = v___x_5371_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
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
                v___x_5394_ = lean_uint8_once(
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
                    v___x_5395_ = lean_box(0);
                    v___x_5396_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_5396_ == 0 {
                        if v___x_5394_ == 0 {
                            v_a_5353_ = v_val_5393_;
                            state = 7;
                            continue;
                        } else {
                            v___x_5397_ = 0usize;
                            v___x_5398_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_2466__overap_5399_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_5315_,
                                    v___f_5317_,
                                    v___x_5391_,
                                    v___x_5397_,
                                    v___x_5398_,
                                    v___x_5395_,
                                );
                            lean_inc_ref(v_a_5307_);
                            v___x_5400_ =
                                lean_apply_2(v___x_2466__overap_5399_, v_a_5307_, lean_box(0));
                            if lean_obj_tag(v___x_5400_) == 0 {
                                lean_dec_ref_known(v___x_5400_, 1);
                                v_a_5353_ = v_val_5393_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v_val_5393_);
                                lean_dec_ref(v_pkgDir_5314_);
                                lean_dec_ref(v_remoteUrl_5306_);
                                lean_dec_ref(v_relPkgDir_5305_);
                                lean_dec_ref(v_manifestEntry_5303_);
                                v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
                                v_isSharedCheck_5408_ = (!lean_is_exclusive(v___x_5400_)) as u8;
                                if v_isSharedCheck_5408_ == 0 {
                                    v___x_5403_ = v___x_5400_;
                                    v_isShared_5404_ = v_isSharedCheck_5408_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_5401_);
                                    lean_dec(v___x_5400_);
                                    v___x_5403_ = lean_box(0);
                                    v_isShared_5404_ = v_isSharedCheck_5408_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5409_ = 0usize;
                        v___x_5410_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_2476__overap_5411_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_5315_,
                                v___f_5317_,
                                v___x_5391_,
                                v___x_5409_,
                                v___x_5410_,
                                v___x_5395_,
                            );
                        lean_inc_ref(v_a_5307_);
                        v___x_5412_ =
                            lean_apply_2(v___x_2476__overap_5411_, v_a_5307_, lean_box(0));
                        if lean_obj_tag(v___x_5412_) == 0 {
                            lean_dec_ref_known(v___x_5412_, 1);
                            v_a_5353_ = v_val_5393_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v_val_5393_);
                            lean_dec_ref(v_pkgDir_5314_);
                            lean_dec_ref(v_remoteUrl_5306_);
                            lean_dec_ref(v_relPkgDir_5305_);
                            lean_dec_ref(v_manifestEntry_5303_);
                            v_a_5413_ = lean_ctor_get(v___x_5412_, 0);
                            v_isSharedCheck_5420_ = (!lean_is_exclusive(v___x_5412_)) as u8;
                            if v_isSharedCheck_5420_ == 0 {
                                v___x_5415_ = v___x_5412_;
                                v_isShared_5416_ = v_isSharedCheck_5420_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_5413_);
                                lean_dec(v___x_5412_);
                                v___x_5415_ = lean_box(0);
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
                    v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
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
                    v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
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
    mut v_manifestEntry_5425_: *mut LeanObject,
    mut v_wsDir_5426_: *mut LeanObject,
    mut v_relPkgDir_5427_: *mut LeanObject,
    mut v_remoteUrl_5428_: *mut LeanObject,
    mut v_a_5429_: *mut LeanObject,
    mut v_a_5430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5431_: *mut LeanObject = core::ptr::null_mut();
    v_res_5431_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep(
        v_manifestEntry_5425_,
        v_wsDir_5426_,
        v_relPkgDir_5427_,
        v_remoteUrl_5428_,
        v_a_5429_,
    );
    lean_dec_ref(v_a_5429_);
    return v_res_5431_;
}
pub unsafe fn l_Lake_PackageEntry_materialize(
    mut v_manifestEntry_5433_: *mut LeanObject,
    mut v_lakeEnv_5434_: *mut LeanObject,
    mut v_wsDir_5435_: *mut LeanObject,
    mut v_relPkgsDir_5436_: *mut LeanObject,
    mut v_a_5437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: u8 = 0;
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: u8 = 0;
    let mut v___x_5458_: usize = 0;
    let mut v___x_5459_: usize = 0;
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5464_: u8 = 0;
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v___x_5469_: usize = 0;
    let mut v___x_5470_: usize = 0;
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5475_: u8 = 0;
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut v_src_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5486_: u8 = 0;
    let mut v_pkgDir_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: u8 = 0;
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: u8 = 0;
    let mut v___x_5506_: usize = 0;
    let mut v___x_5507_: usize = 0;
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5512_: u8 = 0;
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5516_: u8 = 0;
    let mut v___x_5517_: usize = 0;
    let mut v___x_5518_: usize = 0;
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5523_: u8 = 0;
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5527_: u8 = 0;
    let mut v_a_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5539_: u8 = 0;
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5543_: u8 = 0;
    let mut v_a_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5547_: u8 = 0;
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5551_: u8 = 0;
    let mut v_val_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: u8 = 0;
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: u8 = 0;
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: u8 = 0;
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: u8 = 0;
    let mut v___x_5571_: usize = 0;
    let mut v___x_5572_: usize = 0;
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5577_: u8 = 0;
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut v___x_5582_: usize = 0;
    let mut v___x_5583_: usize = 0;
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5588_: u8 = 0;
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5592_: u8 = 0;
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v_name_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_url_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subDir_x3f_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: u8 = 0;
    let mut v_sname_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5620_: u8 = 0;
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5624_: u8 = 0;
    let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5632_: u8 = 0;
    let mut v_val_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: u8 = 0;
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: u8 = 0;
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: u8 = 0;
    let mut v___x_5655_: usize = 0;
    let mut v___x_5656_: usize = 0;
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5661_: u8 = 0;
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5665_: u8 = 0;
    let mut v___x_5666_: usize = 0;
    let mut v___x_5667_: usize = 0;
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5676_: u8 = 0;
    let mut v___y_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: u8 = 0;
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relGitDir_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gitDir_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5708_: u8 = 0;
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5712_: u8 = 0;
    let mut v___y_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5720_: u8 = 0;
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut v_a_5726_: u8 = 0;
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: u8 = 0;
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5738_: u8 = 0;
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: u8 = 0;
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: u8 = 0;
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5749_: u8 = 0;
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5753_: u8 = 0;
    let mut v___x_5754_: usize = 0;
    let mut v___x_5755_: usize = 0;
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5760_: u8 = 0;
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5764_: u8 = 0;
    let mut v___y_5766_: u8 = 0;
    let mut v_a_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: u8 = 0;
    let mut v_pkgUrlMap_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: u8 = 0;
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: u8 = 0;
    let mut v_pkgUrlMap_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: u8 = 0;
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: u8 = 0;
    let mut v___x_5788_: usize = 0;
    let mut v___x_5789_: usize = 0;
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5794_: u8 = 0;
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5798_: u8 = 0;
    let mut v___x_5799_: usize = 0;
    let mut v___x_5800_: usize = 0;
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5805_: u8 = 0;
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5809_: u8 = 0;
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: u8 = 0;
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: u8 = 0;
    let mut v___x_5814_: usize = 0;
    let mut v___x_5815_: usize = 0;
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5820_: u8 = 0;
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5824_: u8 = 0;
    let mut v___x_5825_: usize = 0;
    let mut v___x_5826_: usize = 0;
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5831_: u8 = 0;
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_src_5480_ = lean_ctor_get(v_manifestEntry_5433_, 4);
                lean_inc_ref(v_src_5480_);
                if lean_obj_tag(v_src_5480_) == 0 {
                    lean_dec_ref(v_relPkgsDir_5436_);
                    v_name_5481_ = lean_ctor_get(v_manifestEntry_5433_, 0);
                    v_manifestFile_x3f_5482_ = lean_ctor_get(v_manifestEntry_5433_, 3);
                    v_dir_5483_ = lean_ctor_get(v_src_5480_, 0);
                    v_isSharedCheck_5597_ = (!lean_is_exclusive(v_src_5480_)) as u8;
                    if v_isSharedCheck_5597_ == 0 {
                        v___x_5485_ = v_src_5480_;
                        v_isShared_5486_ = v_isSharedCheck_5597_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_dir_5483_);
                        lean_dec(v_src_5480_);
                        v___x_5485_ = lean_box(0);
                        v_isShared_5486_ = v_isSharedCheck_5597_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_name_5598_ = lean_ctor_get(v_manifestEntry_5433_, 0);
                    v_manifestFile_x3f_5599_ = lean_ctor_get(v_manifestEntry_5433_, 3);
                    v_url_5600_ = lean_ctor_get(v_src_5480_, 0);
                    lean_inc_ref(v_url_5600_);
                    v_rev_5601_ = lean_ctor_get(v_src_5480_, 1);
                    lean_inc_ref(v_rev_5601_);
                    v_subDir_x3f_5602_ = lean_ctor_get(v_src_5480_, 3);
                    lean_inc(v_subDir_x3f_5602_);
                    lean_dec_ref_known(v_src_5480_, 4);
                    v___x_5603_ = 0;
                    lean_inc(v_name_5598_);
                    v_sname_5604_ = l_Lean_Name_toString(v_name_5598_, v___x_5603_);
                    lean_inc_ref(v_sname_5604_);
                    v_relGitDir_5695_ = l_Lake_joinRelative(v_relPkgsDir_5436_, v_sname_5604_);
                    lean_inc_ref(v_relGitDir_5695_);
                    lean_inc_ref(v_wsDir_5435_);
                    v_gitDir_5700_ = l_Lake_joinRelative(v_wsDir_5435_, v_relGitDir_5695_);
                    v___x_5777_ = l_System_FilePath_isDir(v_gitDir_5700_);
                    v___x_5810_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_5811_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
                    if v___x_5811_ == 0 {
                        state = 51;
                        continue;
                    } else {
                        v___x_5812_ = lean_box(0);
                        v___x_5813_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                        if v___x_5813_ == 0 {
                            if v___x_5811_ == 0 {
                                state = 51;
                                continue;
                            } else {
                                v___x_5814_ = 0usize;
                                v___x_5815_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                v___x_5816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5810_, v___x_5814_, v___x_5815_, v___x_5812_, v_a_5437_);
                                if lean_obj_tag(v___x_5816_) == 0 {
                                    lean_dec_ref_known(v___x_5816_, 1);
                                    state = 51;
                                    continue;
                                } else {
                                    lean_dec_ref(v_gitDir_5700_);
                                    lean_dec_ref(v_relGitDir_5695_);
                                    lean_dec_ref(v_sname_5604_);
                                    lean_dec(v_subDir_x3f_5602_);
                                    lean_dec_ref(v_rev_5601_);
                                    lean_dec_ref(v_url_5600_);
                                    lean_dec_ref(v_wsDir_5435_);
                                    lean_dec_ref(v_manifestEntry_5433_);
                                    v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
                                    v_isSharedCheck_5824_ = (!lean_is_exclusive(v___x_5816_)) as u8;
                                    if v_isSharedCheck_5824_ == 0 {
                                        v___x_5819_ = v___x_5816_;
                                        v_isShared_5820_ = v_isSharedCheck_5824_;
                                        state = 56;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5817_);
                                        lean_dec(v___x_5816_);
                                        v___x_5819_ = lean_box(0);
                                        v_isShared_5820_ = v_isSharedCheck_5824_;
                                        state = 56;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_5825_ = 0usize;
                            v___x_5826_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_5827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5810_, v___x_5825_, v___x_5826_, v___x_5812_, v_a_5437_);
                            if lean_obj_tag(v___x_5827_) == 0 {
                                lean_dec_ref_known(v___x_5827_, 1);
                                state = 51;
                                continue;
                            } else {
                                lean_dec_ref(v_gitDir_5700_);
                                lean_dec_ref(v_relGitDir_5695_);
                                lean_dec_ref(v_sname_5604_);
                                lean_dec(v_subDir_x3f_5602_);
                                lean_dec_ref(v_rev_5601_);
                                lean_dec_ref(v_url_5600_);
                                lean_dec_ref(v_wsDir_5435_);
                                lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5828_ = lean_ctor_get(v___x_5827_, 0);
                                v_isSharedCheck_5835_ = (!lean_is_exclusive(v___x_5827_)) as u8;
                                if v_isSharedCheck_5835_ == 0 {
                                    v___x_5830_ = v___x_5827_;
                                    v_isShared_5831_ = v_isSharedCheck_5835_;
                                    state = 58;
                                    continue;
                                } else {
                                    lean_inc(v_a_5828_);
                                    lean_dec(v___x_5827_);
                                    v___x_5830_ = lean_box(0);
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
                v___x_5444_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5444_, 0, v___y_5441_);
                lean_ctor_set(v___x_5444_, 1, v___y_5442_);
                lean_ctor_set(v___x_5444_, 2, v___y_5440_);
                lean_ctor_set(v___x_5444_, 3, v_a_5443_);
                lean_ctor_set(v___x_5444_, 4, v_manifestEntry_5433_);
                v___x_5445_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5445_, 0, v___x_5444_);
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
                    v___x_5456_ = lean_box(0);
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
                            if lean_obj_tag(v___x_5460_) == 0 {
                                lean_dec_ref_known(v___x_5460_, 1);
                                v___y_5440_ = v___y_5448_;
                                v___y_5441_ = v___y_5447_;
                                v___y_5442_ = v___y_5451_;
                                v_a_5443_ = v_val_5453_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_val_5453_);
                                lean_dec_ref(v___y_5451_);
                                lean_dec_ref(v___y_5448_);
                                lean_dec_ref(v___y_5447_);
                                lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
                                v_isSharedCheck_5468_ = (!lean_is_exclusive(v___x_5460_)) as u8;
                                if v_isSharedCheck_5468_ == 0 {
                                    v___x_5463_ = v___x_5460_;
                                    v_isShared_5464_ = v_isSharedCheck_5468_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_5461_);
                                    lean_dec(v___x_5460_);
                                    v___x_5463_ = lean_box(0);
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
                        if lean_obj_tag(v___x_5471_) == 0 {
                            lean_dec_ref_known(v___x_5471_, 1);
                            v___y_5440_ = v___y_5448_;
                            v___y_5441_ = v___y_5447_;
                            v___y_5442_ = v___y_5451_;
                            v_a_5443_ = v_val_5453_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_val_5453_);
                            lean_dec_ref(v___y_5451_);
                            lean_dec_ref(v___y_5448_);
                            lean_dec_ref(v___y_5447_);
                            lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5472_ = lean_ctor_get(v___x_5471_, 0);
                            v_isSharedCheck_5479_ = (!lean_is_exclusive(v___x_5471_)) as u8;
                            if v_isSharedCheck_5479_ == 0 {
                                v___x_5474_ = v___x_5471_;
                                v_isShared_5475_ = v_isSharedCheck_5479_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5472_);
                                lean_dec(v___x_5471_);
                                v___x_5474_ = lean_box(0);
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
                    v_reuseFailAlloc_5467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5461_);
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
                    v_reuseFailAlloc_5478_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
                    v___x_5477_ = v_reuseFailAlloc_5478_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5477_;
            }
            7 => {
                lean_inc_ref(v_dir_5483_);
                v_pkgDir_5487_ = l_Lake_joinRelative(v_wsDir_5435_, v_dir_5483_);
                lean_inc_ref(v_pkgDir_5487_);
                v___x_5488_ = l_Lake_resolvePath(v_pkgDir_5487_);
                v___x_5489_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                v___x_5564_ = lean_unsigned_to_nat(0);
                v___x_5565_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_5593_ = lean_string_utf8_byte_size(v___x_5488_);
                v___x_5594_ = lean_nat_dec_eq(v___x_5593_, v___x_5564_);
                if v___x_5594_ == 0 {
                    v___x_5595_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5595_, 0, v___x_5488_);
                    v_val_5567_ = v___x_5595_;
                    state = 20;
                    continue;
                } else {
                    lean_dec_ref(v___x_5488_);
                    v___x_5596_ = lean_box(0);
                    v_val_5567_ = v___x_5596_;
                    state = 20;
                    continue;
                }
            }
            8 => {
                v___x_5493_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5493_, 0, v___y_5491_);
                lean_ctor_set(v___x_5493_, 1, v_dir_5483_);
                lean_ctor_set(v___x_5493_, 2, v___x_5489_);
                lean_ctor_set(v___x_5493_, 3, v_a_5492_);
                lean_ctor_set(v___x_5493_, 4, v_manifestEntry_5433_);
                if v_isShared_5486_ == 0 {
                    lean_ctor_set(v___x_5485_, 0, v___x_5493_);
                    v___x_5495_ = v___x_5485_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5496_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5493_);
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
                    v___x_5504_ = lean_box(0);
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
                            if lean_obj_tag(v___x_5508_) == 0 {
                                lean_dec_ref_known(v___x_5508_, 1);
                                v___y_5491_ = v___y_5500_;
                                v_a_5492_ = v_val_5501_;
                                state = 8;
                                continue;
                            } else {
                                lean_dec_ref(v_val_5501_);
                                lean_dec_ref(v___y_5500_);
                                lean_del_object(v___x_5485_);
                                lean_dec_ref(v_dir_5483_);
                                lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5509_ = lean_ctor_get(v___x_5508_, 0);
                                v_isSharedCheck_5516_ = (!lean_is_exclusive(v___x_5508_)) as u8;
                                if v_isSharedCheck_5516_ == 0 {
                                    v___x_5511_ = v___x_5508_;
                                    v_isShared_5512_ = v_isSharedCheck_5516_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_5509_);
                                    lean_dec(v___x_5508_);
                                    v___x_5511_ = lean_box(0);
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
                        if lean_obj_tag(v___x_5519_) == 0 {
                            lean_dec_ref_known(v___x_5519_, 1);
                            v___y_5491_ = v___y_5500_;
                            v_a_5492_ = v_val_5501_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec_ref(v_val_5501_);
                            lean_dec_ref(v___y_5500_);
                            lean_del_object(v___x_5485_);
                            lean_dec_ref(v_dir_5483_);
                            lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5520_ = lean_ctor_get(v___x_5519_, 0);
                            v_isSharedCheck_5527_ = (!lean_is_exclusive(v___x_5519_)) as u8;
                            if v_isSharedCheck_5527_ == 0 {
                                v___x_5522_ = v___x_5519_;
                                v_isShared_5523_ = v_isSharedCheck_5527_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_5520_);
                                lean_dec(v___x_5519_);
                                v___x_5522_ = lean_box(0);
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
                    v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5509_);
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
                    v_reuseFailAlloc_5526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_a_5520_);
                    v___x_5525_ = v_reuseFailAlloc_5526_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5525_;
            }
            15 => {
                if lean_obj_tag(v_a_5529_) == 1 {
                    lean_dec_ref(v_pkgDir_5487_);
                    if lean_obj_tag(v_manifestFile_x3f_5482_) == 1 {
                        v_val_5530_ = lean_ctor_get(v_a_5529_, 0);
                        lean_inc_n(v_val_5530_, 2);
                        lean_dec_ref_known(v_a_5529_, 1);
                        v_val_5531_ = lean_ctor_get(v_manifestFile_x3f_5482_, 0);
                        lean_inc(v_val_5531_);
                        v___x_5532_ = l_Lake_joinRelative(v_val_5530_, v_val_5531_);
                        v___x_5533_ = lean_unsigned_to_nat(0);
                        v___x_5534_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                        v___x_5535_ = l_Lake_Manifest_load(v___x_5532_);
                        if lean_obj_tag(v___x_5535_) == 0 {
                            v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
                            v_isSharedCheck_5543_ = (!lean_is_exclusive(v___x_5535_)) as u8;
                            if v_isSharedCheck_5543_ == 0 {
                                v___x_5538_ = v___x_5535_;
                                v_isShared_5539_ = v_isSharedCheck_5543_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_5536_);
                                lean_dec(v___x_5535_);
                                v___x_5538_ = lean_box(0);
                                v_isShared_5539_ = v_isSharedCheck_5543_;
                                state = 16;
                                continue;
                            }
                        } else {
                            v_a_5544_ = lean_ctor_get(v___x_5535_, 0);
                            v_isSharedCheck_5551_ = (!lean_is_exclusive(v___x_5535_)) as u8;
                            if v_isSharedCheck_5551_ == 0 {
                                v___x_5546_ = v___x_5535_;
                                v_isShared_5547_ = v_isSharedCheck_5551_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_5544_);
                                lean_dec(v___x_5535_);
                                v___x_5546_ = lean_box(0);
                                v_isShared_5547_ = v_isSharedCheck_5551_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        v_val_5552_ = lean_ctor_get(v_a_5529_, 0);
                        lean_inc(v_val_5552_);
                        lean_dec_ref_known(v_a_5529_, 1);
                        v___x_5553_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1;
                        v___y_5491_ = v_val_5552_;
                        v_a_5492_ = v___x_5553_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_inc(v_name_5481_);
                    lean_dec(v_a_5529_);
                    lean_del_object(v___x_5485_);
                    lean_dec_ref(v_dir_5483_);
                    lean_dec_ref(v_manifestEntry_5433_);
                    v___x_5554_ = 0;
                    v___x_5555_ = l_Lean_Name_toString(v_name_5481_, v___x_5554_);
                    v___x_5556_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_5557_ = lean_string_append(v___x_5555_, v___x_5556_);
                    v___x_5558_ = lean_string_append(v___x_5557_, v_pkgDir_5487_);
                    lean_dec_ref(v_pkgDir_5487_);
                    v___x_5559_ = 3;
                    v___x_5560_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_5560_, 0, v___x_5558_);
                    lean_ctor_set_uint8(
                        v___x_5560_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5559_,
                    );
                    lean_inc_ref(v_a_5437_);
                    v___x_5561_ = lean_apply_2(v_a_5437_, v___x_5560_, lean_box(0));
                    v___x_5562_ = lean_box(0);
                    v___x_5563_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5563_, 0, v___x_5562_);
                    return v___x_5563_;
                }
            }
            16 => {
                if v_isShared_5539_ == 0 {
                    lean_ctor_set_tag(v___x_5538_, 1);
                    v___x_5541_ = v___x_5538_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5542_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_a_5536_);
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
                    lean_ctor_set_tag(v___x_5546_, 0);
                    v___x_5549_ = v___x_5546_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
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
                v___x_5568_ = lean_uint8_once(
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
                    v___x_5569_ = lean_box(0);
                    v___x_5570_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                    if v___x_5570_ == 0 {
                        if v___x_5568_ == 0 {
                            v_a_5529_ = v_val_5567_;
                            state = 15;
                            continue;
                        } else {
                            v___x_5571_ = 0usize;
                            v___x_5572_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_5573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5565_, v___x_5571_, v___x_5572_, v___x_5569_, v_a_5437_);
                            if lean_obj_tag(v___x_5573_) == 0 {
                                lean_dec_ref_known(v___x_5573_, 1);
                                v_a_5529_ = v_val_5567_;
                                state = 15;
                                continue;
                            } else {
                                lean_dec(v_val_5567_);
                                lean_dec_ref(v_pkgDir_5487_);
                                lean_del_object(v___x_5485_);
                                lean_dec_ref(v_dir_5483_);
                                lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5574_ = lean_ctor_get(v___x_5573_, 0);
                                v_isSharedCheck_5581_ = (!lean_is_exclusive(v___x_5573_)) as u8;
                                if v_isSharedCheck_5581_ == 0 {
                                    v___x_5576_ = v___x_5573_;
                                    v_isShared_5577_ = v_isSharedCheck_5581_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_inc(v_a_5574_);
                                    lean_dec(v___x_5573_);
                                    v___x_5576_ = lean_box(0);
                                    v_isShared_5577_ = v_isSharedCheck_5581_;
                                    state = 21;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5582_ = 0usize;
                        v___x_5583_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                        v___x_5584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5565_, v___x_5582_, v___x_5583_, v___x_5569_, v_a_5437_);
                        if lean_obj_tag(v___x_5584_) == 0 {
                            lean_dec_ref_known(v___x_5584_, 1);
                            v_a_5529_ = v_val_5567_;
                            state = 15;
                            continue;
                        } else {
                            lean_dec(v_val_5567_);
                            lean_dec_ref(v_pkgDir_5487_);
                            lean_del_object(v___x_5485_);
                            lean_dec_ref(v_dir_5483_);
                            lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5585_ = lean_ctor_get(v___x_5584_, 0);
                            v_isSharedCheck_5592_ = (!lean_is_exclusive(v___x_5584_)) as u8;
                            if v_isSharedCheck_5592_ == 0 {
                                v___x_5587_ = v___x_5584_;
                                v_isShared_5588_ = v_isSharedCheck_5592_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_5585_);
                                lean_dec(v___x_5584_);
                                v___x_5587_ = lean_box(0);
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
                    v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
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
                    v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
                    v___x_5590_ = v_reuseFailAlloc_5591_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5590_;
            }
            25 => {
                if lean_obj_tag(v_a_5610_) == 1 {
                    lean_dec_ref(v___y_5607_);
                    lean_dec_ref(v_sname_5604_);
                    if lean_obj_tag(v_manifestFile_x3f_5599_) == 1 {
                        v_val_5611_ = lean_ctor_get(v_a_5610_, 0);
                        lean_inc_n(v_val_5611_, 2);
                        lean_dec_ref_known(v_a_5610_, 1);
                        v_val_5612_ = lean_ctor_get(v_manifestFile_x3f_5599_, 0);
                        lean_inc(v_val_5612_);
                        v___x_5613_ = l_Lake_joinRelative(v_val_5611_, v_val_5612_);
                        v___x_5614_ = lean_unsigned_to_nat(0);
                        v___x_5615_ =
                            l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                        v___x_5616_ = l_Lake_Manifest_load(v___x_5613_);
                        if lean_obj_tag(v___x_5616_) == 0 {
                            v_a_5617_ = lean_ctor_get(v___x_5616_, 0);
                            v_isSharedCheck_5624_ = (!lean_is_exclusive(v___x_5616_)) as u8;
                            if v_isSharedCheck_5624_ == 0 {
                                v___x_5619_ = v___x_5616_;
                                v_isShared_5620_ = v_isSharedCheck_5624_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_5617_);
                                lean_dec(v___x_5616_);
                                v___x_5619_ = lean_box(0);
                                v_isShared_5620_ = v_isSharedCheck_5624_;
                                state = 26;
                                continue;
                            }
                        } else {
                            v_a_5625_ = lean_ctor_get(v___x_5616_, 0);
                            v_isSharedCheck_5632_ = (!lean_is_exclusive(v___x_5616_)) as u8;
                            if v_isSharedCheck_5632_ == 0 {
                                v___x_5627_ = v___x_5616_;
                                v_isShared_5628_ = v_isSharedCheck_5632_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_5625_);
                                lean_dec(v___x_5616_);
                                v___x_5627_ = lean_box(0);
                                v_isShared_5628_ = v_isSharedCheck_5632_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        v_val_5633_ = lean_ctor_get(v_a_5610_, 0);
                        lean_inc(v_val_5633_);
                        lean_dec_ref_known(v_a_5610_, 1);
                        v___x_5634_ = l___private_Lake_Load_Materialize_0__Lake_PackageEntry_materialize_mkDep___closed__1;
                        v___y_5440_ = v___y_5606_;
                        v___y_5441_ = v_val_5633_;
                        v___y_5442_ = v___y_5609_;
                        v_a_5443_ = v___x_5634_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5610_);
                    lean_dec_ref(v___y_5609_);
                    lean_dec_ref(v___y_5606_);
                    lean_dec_ref(v_manifestEntry_5433_);
                    v___x_5635_ = l___private_Lake_Load_Materialize_0__Lake_Dependency_materialize_mkDep___closed__3;
                    v___x_5636_ = lean_string_append(v_sname_5604_, v___x_5635_);
                    v___x_5637_ = lean_string_append(v___x_5636_, v___y_5607_);
                    lean_dec_ref(v___y_5607_);
                    v___x_5638_ = 3;
                    v___x_5639_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_5639_, 0, v___x_5637_);
                    lean_ctor_set_uint8(
                        v___x_5639_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5638_,
                    );
                    lean_inc_ref(v___y_5608_);
                    v___x_5640_ = lean_apply_2(v___y_5608_, v___x_5639_, lean_box(0));
                    v___x_5641_ = lean_box(0);
                    v___x_5642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5642_, 0, v___x_5641_);
                    return v___x_5642_;
                }
            }
            26 => {
                if v_isShared_5620_ == 0 {
                    lean_ctor_set_tag(v___x_5619_, 1);
                    v___x_5622_ = v___x_5619_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5623_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
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
                    lean_ctor_set_tag(v___x_5627_, 0);
                    v___x_5630_ = v___x_5627_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_a_5625_);
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
                    v___x_5653_ = lean_box(0);
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
                            if lean_obj_tag(v___x_5657_) == 0 {
                                lean_dec_ref_known(v___x_5657_, 1);
                                v___y_5606_ = v___y_5645_;
                                v___y_5607_ = v___y_5646_;
                                v___y_5608_ = v___y_5647_;
                                v___y_5609_ = v___y_5649_;
                                v_a_5610_ = v_val_5650_;
                                state = 25;
                                continue;
                            } else {
                                lean_dec(v_val_5650_);
                                lean_dec_ref(v___y_5649_);
                                lean_dec_ref(v___y_5646_);
                                lean_dec_ref(v___y_5645_);
                                lean_dec_ref(v_sname_5604_);
                                lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5658_ = lean_ctor_get(v___x_5657_, 0);
                                v_isSharedCheck_5665_ = (!lean_is_exclusive(v___x_5657_)) as u8;
                                if v_isSharedCheck_5665_ == 0 {
                                    v___x_5660_ = v___x_5657_;
                                    v_isShared_5661_ = v_isSharedCheck_5665_;
                                    state = 31;
                                    continue;
                                } else {
                                    lean_inc(v_a_5658_);
                                    lean_dec(v___x_5657_);
                                    v___x_5660_ = lean_box(0);
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
                        if lean_obj_tag(v___x_5668_) == 0 {
                            lean_dec_ref_known(v___x_5668_, 1);
                            v___y_5606_ = v___y_5645_;
                            v___y_5607_ = v___y_5646_;
                            v___y_5608_ = v___y_5647_;
                            v___y_5609_ = v___y_5649_;
                            v_a_5610_ = v_val_5650_;
                            state = 25;
                            continue;
                        } else {
                            lean_dec(v_val_5650_);
                            lean_dec_ref(v___y_5649_);
                            lean_dec_ref(v___y_5646_);
                            lean_dec_ref(v___y_5645_);
                            lean_dec_ref(v_sname_5604_);
                            lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5669_ = lean_ctor_get(v___x_5668_, 0);
                            v_isSharedCheck_5676_ = (!lean_is_exclusive(v___x_5668_)) as u8;
                            if v_isSharedCheck_5676_ == 0 {
                                v___x_5671_ = v___x_5668_;
                                v_isShared_5672_ = v_isSharedCheck_5676_;
                                state = 33;
                                continue;
                            } else {
                                lean_inc(v_a_5669_);
                                lean_dec(v___x_5668_);
                                v___x_5671_ = lean_box(0);
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
                    v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
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
                    v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
                    v___x_5674_ = v_reuseFailAlloc_5675_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5674_;
            }
            35 => {
                lean_inc_ref(v___y_5679_);
                v_pkgDir_5681_ = l_Lake_joinRelative(v_wsDir_5435_, v___y_5679_);
                lean_inc_ref(v_pkgDir_5681_);
                v___x_5682_ = l_Lake_resolvePath(v_pkgDir_5681_);
                v___x_5683_ = lean_unsigned_to_nat(0);
                v___x_5684_ = l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                v___x_5685_ = lean_string_utf8_byte_size(v___x_5682_);
                v___x_5686_ = lean_nat_dec_eq(v___x_5685_, v___x_5683_);
                if v___x_5686_ == 0 {
                    v___x_5687_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5687_, 0, v___x_5682_);
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
                    lean_dec_ref(v___x_5682_);
                    v___x_5688_ = lean_box(0);
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
                if lean_obj_tag(v___x_5692_) == 0 {
                    v___x_5693_ = l_Lake_instInhabitedMaterializedDep_default___closed__0;
                    v___y_5678_ = v___y_5690_;
                    v___y_5679_ = v___y_5691_;
                    v___y_5680_ = v___x_5693_;
                    state = 35;
                    continue;
                } else {
                    v_val_5694_ = lean_ctor_get(v___x_5692_, 0);
                    lean_inc(v_val_5694_);
                    lean_dec_ref_known(v___x_5692_, 1);
                    v___y_5678_ = v___y_5690_;
                    v___y_5679_ = v___y_5691_;
                    v___y_5680_ = v_val_5694_;
                    state = 35;
                    continue;
                }
            }
            37 => {
                if lean_obj_tag(v_subDir_x3f_5602_) == 0 {
                    v___y_5690_ = v___y_5697_;
                    v___y_5691_ = v_relGitDir_5695_;
                    state = 36;
                    continue;
                } else {
                    v_val_5698_ = lean_ctor_get(v_subDir_x3f_5602_, 0);
                    lean_inc(v_val_5698_);
                    lean_dec_ref_known(v_subDir_x3f_5602_, 1);
                    v___x_5699_ = l_Lake_joinRelative(v_relGitDir_5695_, v_val_5698_);
                    v___y_5690_ = v___y_5697_;
                    v___y_5691_ = v___x_5699_;
                    state = 36;
                    continue;
                }
            }
            38 => {
                lean_inc_ref(v_sname_5604_);
                v___x_5704_ = l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___at___00__private_Lake_Load_Materialize_0__Lake_materializeGitRepo_spec__0(v_a_5437_, v_sname_5604_, v_gitDir_5700_, v___y_5703_, v___y_5702_);
                if lean_obj_tag(v___x_5704_) == 0 {
                    lean_dec_ref_known(v___x_5704_, 1);
                    v___y_5697_ = v_a_5437_;
                    state = 37;
                    continue;
                } else {
                    lean_dec_ref(v_relGitDir_5695_);
                    lean_dec_ref(v_sname_5604_);
                    lean_dec(v_subDir_x3f_5602_);
                    lean_dec_ref(v_url_5600_);
                    lean_dec_ref(v_wsDir_5435_);
                    lean_dec_ref(v_manifestEntry_5433_);
                    v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
                    v_isSharedCheck_5712_ = (!lean_is_exclusive(v___x_5704_)) as u8;
                    if v_isSharedCheck_5712_ == 0 {
                        v___x_5707_ = v___x_5704_;
                        v_isShared_5708_ = v_isSharedCheck_5712_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_a_5705_);
                        lean_dec(v___x_5704_);
                        v___x_5707_ = lean_box(0);
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
                    v_reuseFailAlloc_5711_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5711_, 0, v_a_5705_);
                    v___x_5710_ = v_reuseFailAlloc_5711_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5710_;
            }
            41 => {
                v___x_5715_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5715_, 0, v_rev_5601_);
                lean_inc_ref(v_sname_5604_);
                v___x_5716_ = l___private_Lake_Load_Materialize_0__Lake_cloneGitPkg___at___00__private_Lake_Load_Materialize_0__Lake_updateGitRepo_spec__0(v_a_5437_, v_sname_5604_, v_gitDir_5700_, v___y_5714_, v___x_5715_);
                if lean_obj_tag(v___x_5716_) == 0 {
                    lean_dec_ref_known(v___x_5716_, 1);
                    v___y_5697_ = v_a_5437_;
                    state = 37;
                    continue;
                } else {
                    lean_dec_ref(v_relGitDir_5695_);
                    lean_dec_ref(v_sname_5604_);
                    lean_dec(v_subDir_x3f_5602_);
                    lean_dec_ref(v_url_5600_);
                    lean_dec_ref(v_wsDir_5435_);
                    lean_dec_ref(v_manifestEntry_5433_);
                    v_a_5717_ = lean_ctor_get(v___x_5716_, 0);
                    v_isSharedCheck_5724_ = (!lean_is_exclusive(v___x_5716_)) as u8;
                    if v_isSharedCheck_5724_ == 0 {
                        v___x_5719_ = v___x_5716_;
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_a_5717_);
                        lean_dec(v___x_5716_);
                        v___x_5719_ = lean_box(0);
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
                    v_reuseFailAlloc_5723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
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
                    lean_dec_ref(v_gitDir_5700_);
                    v___y_5697_ = v_a_5437_;
                    state = 37;
                    continue;
                } else {
                    v___x_5727_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__0;
                    lean_inc_ref(v_sname_5604_);
                    v___x_5728_ = lean_string_append(v_sname_5604_, v___x_5727_);
                    v___x_5729_ = lean_string_append(v___x_5728_, v_gitDir_5700_);
                    lean_dec_ref(v_gitDir_5700_);
                    v___x_5730_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__1;
                    v___x_5731_ = lean_string_append(v___x_5729_, v___x_5730_);
                    v___x_5732_ = 2;
                    v___x_5733_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_5733_, 0, v___x_5731_);
                    lean_ctor_set_uint8(
                        v___x_5733_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5732_,
                    );
                    lean_inc_ref(v_a_5437_);
                    v___x_5734_ = lean_apply_2(v_a_5437_, v___x_5733_, lean_box(0));
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
                    v___x_5741_ = lean_box(0);
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
                            if lean_obj_tag(v___x_5745_) == 0 {
                                lean_dec_ref_known(v___x_5745_, 1);
                                v_a_5726_ = v_val_5738_;
                                state = 44;
                                continue;
                            } else {
                                lean_dec_ref(v_gitDir_5700_);
                                lean_dec_ref(v_relGitDir_5695_);
                                lean_dec_ref(v_sname_5604_);
                                lean_dec(v_subDir_x3f_5602_);
                                lean_dec_ref(v_url_5600_);
                                lean_dec_ref(v_wsDir_5435_);
                                lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5746_ = lean_ctor_get(v___x_5745_, 0);
                                v_isSharedCheck_5753_ = (!lean_is_exclusive(v___x_5745_)) as u8;
                                if v_isSharedCheck_5753_ == 0 {
                                    v___x_5748_ = v___x_5745_;
                                    v_isShared_5749_ = v_isSharedCheck_5753_;
                                    state = 46;
                                    continue;
                                } else {
                                    lean_inc(v_a_5746_);
                                    lean_dec(v___x_5745_);
                                    v___x_5748_ = lean_box(0);
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
                        if lean_obj_tag(v___x_5756_) == 0 {
                            lean_dec_ref_known(v___x_5756_, 1);
                            v_a_5726_ = v_val_5738_;
                            state = 44;
                            continue;
                        } else {
                            lean_dec_ref(v_gitDir_5700_);
                            lean_dec_ref(v_relGitDir_5695_);
                            lean_dec_ref(v_sname_5604_);
                            lean_dec(v_subDir_x3f_5602_);
                            lean_dec_ref(v_url_5600_);
                            lean_dec_ref(v_wsDir_5435_);
                            lean_dec_ref(v_manifestEntry_5433_);
                            v_a_5757_ = lean_ctor_get(v___x_5756_, 0);
                            v_isSharedCheck_5764_ = (!lean_is_exclusive(v___x_5756_)) as u8;
                            if v_isSharedCheck_5764_ == 0 {
                                v___x_5759_ = v___x_5756_;
                                v_isShared_5760_ = v_isSharedCheck_5764_;
                                state = 48;
                                continue;
                            } else {
                                lean_inc(v_a_5757_);
                                lean_dec(v___x_5756_);
                                v___x_5759_ = lean_box(0);
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
                    v_reuseFailAlloc_5752_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5746_);
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
                    v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
                    v___x_5762_ = v_reuseFailAlloc_5763_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_5762_;
            }
            50 => {
                v___x_5768_ = lean_alloc_closure(
                    l_instDecidableEqString___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                v___x_5769_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5769_, 0, v_rev_5601_);
                lean_inc_ref(v___x_5769_);
                v___x_5770_ =
                    l_Option_instDecidableEq___redArg(v___x_5768_, v_a_5767_, v___x_5769_);
                if v___x_5770_ == 0 {
                    v_pkgUrlMap_5771_ = lean_ctor_get(v_lakeEnv_5434_, 5);
                    v___x_5772_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_5771_, v_name_5598_);
                    if lean_obj_tag(v___x_5772_) == 0 {
                        lean_inc_ref(v_url_5600_);
                        v___y_5702_ = v___x_5769_;
                        v___y_5703_ = v_url_5600_;
                        state = 38;
                        continue;
                    } else {
                        v_val_5773_ = lean_ctor_get(v___x_5772_, 0);
                        lean_inc(v_val_5773_);
                        lean_dec_ref_known(v___x_5772_, 1);
                        v___y_5702_ = v___x_5769_;
                        v___y_5703_ = v_val_5773_;
                        state = 38;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_5769_, 1);
                    lean_inc_ref(v_gitDir_5700_);
                    v___x_5774_ = l_Lake_GitRepo_hasNoDiff(v_gitDir_5700_);
                    v___x_5775_ = lean_unsigned_to_nat(0);
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
                    v_pkgUrlMap_5779_ = lean_ctor_get(v_lakeEnv_5434_, 5);
                    v___x_5780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgUrlMap_5779_, v_name_5598_);
                    if lean_obj_tag(v___x_5780_) == 0 {
                        lean_inc_ref(v_url_5600_);
                        v___y_5714_ = v_url_5600_;
                        state = 41;
                        continue;
                    } else {
                        v_val_5781_ = lean_ctor_get(v___x_5780_, 0);
                        lean_inc(v_val_5781_);
                        lean_dec_ref_known(v___x_5780_, 1);
                        v___y_5714_ = v_val_5781_;
                        state = 41;
                        continue;
                    }
                } else {
                    v___x_5782_ = l_Lake_PackageEntry_materialize___closed__0;
                    lean_inc_ref(v_gitDir_5700_);
                    v___x_5783_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_5782_, v_gitDir_5700_);
                    v___x_5784_ =
                        l___private_Lake_Load_Materialize_0__Lake_updateGitPkg___closed__2;
                    v___x_5785_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__5);
                    if v___x_5785_ == 0 {
                        v___y_5766_ = v___x_5777_;
                        v_a_5767_ = v___x_5783_;
                        state = 50;
                        continue;
                    } else {
                        v___x_5786_ = lean_box(0);
                        v___x_5787_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__6);
                        if v___x_5787_ == 0 {
                            if v___x_5785_ == 0 {
                                v___y_5766_ = v___x_5777_;
                                v_a_5767_ = v___x_5783_;
                                state = 50;
                                continue;
                            } else {
                                v___x_5788_ = 0usize;
                                v___x_5789_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                                v___x_5790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5784_, v___x_5788_, v___x_5789_, v___x_5786_, v_a_5437_);
                                if lean_obj_tag(v___x_5790_) == 0 {
                                    lean_dec_ref_known(v___x_5790_, 1);
                                    v___y_5766_ = v___x_5777_;
                                    v_a_5767_ = v___x_5783_;
                                    state = 50;
                                    continue;
                                } else {
                                    lean_dec(v___x_5783_);
                                    lean_dec_ref(v_gitDir_5700_);
                                    lean_dec_ref(v_relGitDir_5695_);
                                    lean_dec_ref(v_sname_5604_);
                                    lean_dec(v_subDir_x3f_5602_);
                                    lean_dec_ref(v_rev_5601_);
                                    lean_dec_ref(v_url_5600_);
                                    lean_dec_ref(v_wsDir_5435_);
                                    lean_dec_ref(v_manifestEntry_5433_);
                                    v_a_5791_ = lean_ctor_get(v___x_5790_, 0);
                                    v_isSharedCheck_5798_ = (!lean_is_exclusive(v___x_5790_)) as u8;
                                    if v_isSharedCheck_5798_ == 0 {
                                        v___x_5793_ = v___x_5790_;
                                        v_isShared_5794_ = v_isSharedCheck_5798_;
                                        state = 52;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5791_);
                                        lean_dec(v___x_5790_);
                                        v___x_5793_ = lean_box(0);
                                        v_isShared_5794_ = v_isSharedCheck_5798_;
                                        state = 52;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_5799_ = 0usize;
                            v___x_5800_ = lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7_once), _init_l___private_Lake_Load_Materialize_0__Lake_updateGitRepo___closed__7);
                            v___x_5801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Materialize_0__Lake_updateGitPkg_spec__0(v___x_5784_, v___x_5799_, v___x_5800_, v___x_5786_, v_a_5437_);
                            if lean_obj_tag(v___x_5801_) == 0 {
                                lean_dec_ref_known(v___x_5801_, 1);
                                v___y_5766_ = v___x_5777_;
                                v_a_5767_ = v___x_5783_;
                                state = 50;
                                continue;
                            } else {
                                lean_dec(v___x_5783_);
                                lean_dec_ref(v_gitDir_5700_);
                                lean_dec_ref(v_relGitDir_5695_);
                                lean_dec_ref(v_sname_5604_);
                                lean_dec(v_subDir_x3f_5602_);
                                lean_dec_ref(v_rev_5601_);
                                lean_dec_ref(v_url_5600_);
                                lean_dec_ref(v_wsDir_5435_);
                                lean_dec_ref(v_manifestEntry_5433_);
                                v_a_5802_ = lean_ctor_get(v___x_5801_, 0);
                                v_isSharedCheck_5809_ = (!lean_is_exclusive(v___x_5801_)) as u8;
                                if v_isSharedCheck_5809_ == 0 {
                                    v___x_5804_ = v___x_5801_;
                                    v_isShared_5805_ = v_isSharedCheck_5809_;
                                    state = 54;
                                    continue;
                                } else {
                                    lean_inc(v_a_5802_);
                                    lean_dec(v___x_5801_);
                                    v___x_5804_ = lean_box(0);
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
                    v_reuseFailAlloc_5797_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_a_5791_);
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
                    v_reuseFailAlloc_5808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5808_, 0, v_a_5802_);
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
                    v_reuseFailAlloc_5823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_a_5817_);
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
                    v_reuseFailAlloc_5834_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5828_);
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
    mut v_manifestEntry_5836_: *mut LeanObject,
    mut v_lakeEnv_5837_: *mut LeanObject,
    mut v_wsDir_5838_: *mut LeanObject,
    mut v_relPkgsDir_5839_: *mut LeanObject,
    mut v_a_5840_: *mut LeanObject,
    mut v_a_5841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5842_: *mut LeanObject = core::ptr::null_mut();
    v_res_5842_ = l_Lake_PackageEntry_materialize(
        v_manifestEntry_5836_,
        v_lakeEnv_5837_,
        v_wsDir_5838_,
        v_relPkgsDir_5839_,
        v_a_5840_,
    );
    lean_dec_ref(v_a_5840_);
    lean_dec_ref(v_lakeEnv_5837_);
    return v_res_5842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Materialize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Env(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Manifest(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Reservoir(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instInhabitedMaterializedDep_default =
        _init_l_Lake_instInhabitedMaterializedDep_default();
    lean_mark_persistent(l_Lake_instInhabitedMaterializedDep_default);
    l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
    lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Materialize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Materialize(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Env(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Load_Manifest(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Reservoir(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Materialize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Materialize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Load_Materialize(builtin);
}
