// Lean compiler output
// Module: Lake.Load.Package
// Imports: Lake.Load.Config Lake.Config.Package Lake.Config.LakefileConfig Lake.Util.IO Lake.Load.Lean Lake.Load.Toml
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_extension,
};
use crate::r#gen::Init::System::IO::l_System_FilePath_pathExists;
use crate::r#gen::Init::System::Platform::l_System_Platform_target;
use crate::r#gen::Lake::Config::Env::l_Lake_Env_leanSearchPath;
use crate::r#gen::Lake::Config::LakefileConfig::{
    initialize_Lake_Config_LakefileConfig, runtime_initialize_Lake_Config_LakefileConfig,
};
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, runtime_initialize_Lake_Config_Package,
};
use crate::r#gen::Lake::Load::Config::{
    initialize_Lake_Load_Config, runtime_initialize_Lake_Load_Config,
};
use crate::r#gen::Lake::Load::Lean::{
    initialize_Lake_Load_Lean, l_Lake_loadLeanConfig, runtime_initialize_Lake_Load_Lean,
};
use crate::r#gen::Lake::Load::Toml::{
    initialize_Lake_Load_Toml, l_Lake_loadTomlConfig, runtime_initialize_Lake_Load_Toml,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lake::Util::IO::{
    initialize_Lake_Util_IO, l_Lake_resolvePath, runtime_initialize_Lake_Util_IO,
};
use crate::r#gen::Lean::Util::Path::l_Lean_searchPathRef;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_nat_dec_eq, lean_string_dec_eq,
    lean_string_utf8_byte_size,
};
use crate::ffi::lean_st_ref_set;
pub static l_Lake_mkPackage___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_mkPackage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkPackage___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_mkPackage___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [45, 0],
    };
static mut l_Lake_mkPackage___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkPackage___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_mkPackage___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [46, 116, 97, 114, 46, 103, 122, 0],
    };
static mut l_Lake_mkPackage___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkPackage___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_configFileExists___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_Lake_configFileExists___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_configFileExists___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_configFileExists___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 111, 109, 108, 0],
    };
static mut l_Lake_configFileExists___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_configFileExists___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__0_value: crate::leanh::LeanStringObject<49> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 49,
        m_capacity: 49,
        m_length: 48,
        m_data: [
            58, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 104, 97,
            115, 32, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 102, 105, 108, 101,
            32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 58, 32, 0,
        ],
    };
static mut l_Lake_resolveConfigFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_resolveConfigFile___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_resolveConfigFile___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__3_value: crate::leanh::LeanStringObject<33> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            58, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 102, 105,
            108, 101, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58, 32, 0,
        ],
    };
static mut l_Lake_resolveConfigFile___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__4_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 32, 0],
    };
static mut l_Lake_resolveConfigFile___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__5_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [32, 97, 110, 100, 32, 0],
    };
static mut l_Lake_resolveConfigFile___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__6_value: crate::leanh::LeanStringObject<26> =
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
            32, 97, 114, 101, 32, 98, 111, 116, 104, 32, 112, 114, 101, 115, 101, 110, 116, 59, 32,
            117, 115, 105, 110, 103, 32, 0,
        ],
    };
static mut l_Lake_resolveConfigFile___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__7_value: crate::leanh::LeanStringObject<53> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 53,
        m_capacity: 53,
        m_length: 52,
        m_data: [
            58, 32, 110, 111, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110,
            32, 102, 105, 108, 101, 32, 119, 105, 116, 104, 32, 97, 32, 115, 117, 112, 112, 111,
            114, 116, 101, 100, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 58, 10, 0,
        ],
    };
static mut l_Lake_resolveConfigFile___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_resolveConfigFile___closed__8_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [10, 0],
    };
static mut l_Lake_resolveConfigFile___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolveConfigFile___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_loadPackage___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [91, 114, 111, 111, 116, 93, 0],
    };
static mut l_Lake_loadPackage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_loadPackage___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_mkPackage(
    mut v_loadCfg_320_: *mut crate::leanh::LeanObject,
    mut v_fileCfg_321_: *mut crate::leanh::LeanObject,
    mut v_wsIdx_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkgDecl_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relPkgDir_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relConfigFile_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remoteUrl_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depConfigs_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDeclMap_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultTargets_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scripts_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultScripts_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postUpdateHooks_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_testDriver_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lintDriver_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origName_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildArchive_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkgDecl_323_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 0);
    crate::leanh::lean_inc_ref(v_pkgDecl_323_);
    v_config_324_ = crate::leanh::lean_ctor_get(v_pkgDecl_323_, 3);
    crate::leanh::lean_inc_ref(v_config_324_);
    v_relPkgDir_325_ = crate::leanh::lean_ctor_get(v_loadCfg_320_, 5);
    v_pkgDir_326_ = crate::leanh::lean_ctor_get(v_loadCfg_320_, 6);
    v_relConfigFile_327_ = crate::leanh::lean_ctor_get(v_loadCfg_320_, 7);
    v_configFile_328_ = crate::leanh::lean_ctor_get(v_loadCfg_320_, 8);
    v_relManifestFile_329_ = crate::leanh::lean_ctor_get(v_loadCfg_320_, 10);
    v_scope_330_ = crate::leanh::lean_ctor_get(v_loadCfg_320_, 14);
    v_remoteUrl_331_ = crate::leanh::lean_ctor_get(v_loadCfg_320_, 15);
    v_depConfigs_332_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 1);
    crate::leanh::lean_inc_ref(v_depConfigs_332_);
    v_targetDecls_333_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 3);
    crate::leanh::lean_inc_ref(v_targetDecls_333_);
    v_targetDeclMap_334_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 4);
    crate::leanh::lean_inc(v_targetDeclMap_334_);
    v_defaultTargets_335_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 5);
    crate::leanh::lean_inc_ref(v_defaultTargets_335_);
    v_scripts_336_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 6);
    crate::leanh::lean_inc(v_scripts_336_);
    v_defaultScripts_337_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 7);
    crate::leanh::lean_inc_ref(v_defaultScripts_337_);
    v_postUpdateHooks_338_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 8);
    crate::leanh::lean_inc_ref(v_postUpdateHooks_338_);
    v_testDriver_339_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 9);
    crate::leanh::lean_inc_ref(v_testDriver_339_);
    v_lintDriver_340_ = crate::leanh::lean_ctor_get(v_fileCfg_321_, 10);
    crate::leanh::lean_inc_ref(v_lintDriver_340_);
    crate::leanh::lean_dec_ref(v_fileCfg_321_);
    v_baseName_341_ = crate::leanh::lean_ctor_get(v_pkgDecl_323_, 0);
    crate::leanh::lean_inc(v_baseName_341_);
    v_keyName_342_ = crate::leanh::lean_ctor_get(v_pkgDecl_323_, 1);
    crate::leanh::lean_inc(v_keyName_342_);
    v_origName_343_ = crate::leanh::lean_ctor_get(v_pkgDecl_323_, 2);
    crate::leanh::lean_inc(v_origName_343_);
    crate::leanh::lean_dec_ref(v_pkgDecl_323_);
    v_buildArchive_344_ = crate::leanh::lean_ctor_get(v_config_324_, 11);
    v___x_345_ = l_Lake_mkPackage___closed__0;
    if crate::leanh::lean_obj_tag(v_buildArchive_344_) == 1 {
        let mut v_val_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_346_ = crate::leanh::lean_ctor_get(v_buildArchive_344_, 0);
        crate::leanh::lean_inc(v_val_346_);
        crate::leanh::lean_inc_ref(v_remoteUrl_331_);
        crate::leanh::lean_inc_ref(v_scope_330_);
        crate::leanh::lean_inc_ref(v_relManifestFile_329_);
        crate::leanh::lean_inc_ref(v_relConfigFile_327_);
        crate::leanh::lean_inc_ref(v_configFile_328_);
        crate::leanh::lean_inc_ref(v_relPkgDir_325_);
        crate::leanh::lean_inc_ref(v_pkgDir_326_);
        v___x_347_ = crate::leanh::lean_alloc_ctor(0, 23, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_347_, 0, v_wsIdx_322_);
        crate::leanh::lean_ctor_set(v___x_347_, 1, v_baseName_341_);
        crate::leanh::lean_ctor_set(v___x_347_, 2, v_keyName_342_);
        crate::leanh::lean_ctor_set(v___x_347_, 3, v_origName_343_);
        crate::leanh::lean_ctor_set(v___x_347_, 4, v_pkgDir_326_);
        crate::leanh::lean_ctor_set(v___x_347_, 5, v_relPkgDir_325_);
        crate::leanh::lean_ctor_set(v___x_347_, 6, v_config_324_);
        crate::leanh::lean_ctor_set(v___x_347_, 7, v_configFile_328_);
        crate::leanh::lean_ctor_set(v___x_347_, 8, v_relConfigFile_327_);
        crate::leanh::lean_ctor_set(v___x_347_, 9, v_relManifestFile_329_);
        crate::leanh::lean_ctor_set(v___x_347_, 10, v_scope_330_);
        crate::leanh::lean_ctor_set(v___x_347_, 11, v_remoteUrl_331_);
        crate::leanh::lean_ctor_set(v___x_347_, 12, v_depConfigs_332_);
        crate::leanh::lean_ctor_set(v___x_347_, 13, v___x_345_);
        crate::leanh::lean_ctor_set(v___x_347_, 14, v_targetDecls_333_);
        crate::leanh::lean_ctor_set(v___x_347_, 15, v_targetDeclMap_334_);
        crate::leanh::lean_ctor_set(v___x_347_, 16, v_defaultTargets_335_);
        crate::leanh::lean_ctor_set(v___x_347_, 17, v_scripts_336_);
        crate::leanh::lean_ctor_set(v___x_347_, 18, v_defaultScripts_337_);
        crate::leanh::lean_ctor_set(v___x_347_, 19, v_postUpdateHooks_338_);
        crate::leanh::lean_ctor_set(v___x_347_, 20, v_val_346_);
        crate::leanh::lean_ctor_set(v___x_347_, 21, v_testDriver_339_);
        crate::leanh::lean_ctor_set(v___x_347_, 22, v_lintDriver_340_);
        return v___x_347_;
    } else {
        let mut v___x_348_: u8 = 0;
        let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_348_ = 0;
        crate::leanh::lean_inc(v_baseName_341_);
        v___x_349_ = l_Lean_Name_toString(v_baseName_341_, v___x_348_);
        v___x_350_ = l_Lake_mkPackage___closed__1;
        v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
        v___x_352_ = l_System_Platform_target;
        v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
        v___x_354_ = l_Lake_mkPackage___closed__2;
        v___x_355_ = lean_string_append(v___x_353_, v___x_354_);
        crate::leanh::lean_inc_ref(v_remoteUrl_331_);
        crate::leanh::lean_inc_ref(v_scope_330_);
        crate::leanh::lean_inc_ref(v_relManifestFile_329_);
        crate::leanh::lean_inc_ref(v_relConfigFile_327_);
        crate::leanh::lean_inc_ref(v_configFile_328_);
        crate::leanh::lean_inc_ref(v_relPkgDir_325_);
        crate::leanh::lean_inc_ref(v_pkgDir_326_);
        v___x_356_ = crate::leanh::lean_alloc_ctor(0, 23, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_356_, 0, v_wsIdx_322_);
        crate::leanh::lean_ctor_set(v___x_356_, 1, v_baseName_341_);
        crate::leanh::lean_ctor_set(v___x_356_, 2, v_keyName_342_);
        crate::leanh::lean_ctor_set(v___x_356_, 3, v_origName_343_);
        crate::leanh::lean_ctor_set(v___x_356_, 4, v_pkgDir_326_);
        crate::leanh::lean_ctor_set(v___x_356_, 5, v_relPkgDir_325_);
        crate::leanh::lean_ctor_set(v___x_356_, 6, v_config_324_);
        crate::leanh::lean_ctor_set(v___x_356_, 7, v_configFile_328_);
        crate::leanh::lean_ctor_set(v___x_356_, 8, v_relConfigFile_327_);
        crate::leanh::lean_ctor_set(v___x_356_, 9, v_relManifestFile_329_);
        crate::leanh::lean_ctor_set(v___x_356_, 10, v_scope_330_);
        crate::leanh::lean_ctor_set(v___x_356_, 11, v_remoteUrl_331_);
        crate::leanh::lean_ctor_set(v___x_356_, 12, v_depConfigs_332_);
        crate::leanh::lean_ctor_set(v___x_356_, 13, v___x_345_);
        crate::leanh::lean_ctor_set(v___x_356_, 14, v_targetDecls_333_);
        crate::leanh::lean_ctor_set(v___x_356_, 15, v_targetDeclMap_334_);
        crate::leanh::lean_ctor_set(v___x_356_, 16, v_defaultTargets_335_);
        crate::leanh::lean_ctor_set(v___x_356_, 17, v_scripts_336_);
        crate::leanh::lean_ctor_set(v___x_356_, 18, v_defaultScripts_337_);
        crate::leanh::lean_ctor_set(v___x_356_, 19, v_postUpdateHooks_338_);
        crate::leanh::lean_ctor_set(v___x_356_, 20, v___x_355_);
        crate::leanh::lean_ctor_set(v___x_356_, 21, v_testDriver_339_);
        crate::leanh::lean_ctor_set(v___x_356_, 22, v_lintDriver_340_);
        return v___x_356_;
    }
}
pub unsafe fn l_Lake_mkPackage___boxed(
    mut v_loadCfg_357_: *mut crate::leanh::LeanObject,
    mut v_fileCfg_358_: *mut crate::leanh::LeanObject,
    mut v_wsIdx_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l_Lake_mkPackage(v_loadCfg_357_, v_fileCfg_358_, v_wsIdx_359_);
    crate::leanh::lean_dec_ref(v_loadCfg_357_);
    return v_res_360_;
}
pub unsafe fn l_Lake_configFileExists(mut v_cfgFile_363_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_cfgFile_363_);
    v___x_365_ = l_System_FilePath_extension(v_cfgFile_363_);
    if crate::leanh::lean_obj_tag(v___x_365_) == 0 {
        let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_leanFile_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_368_: u8 = 0;
        v___x_366_ = l_Lake_configFileExists___closed__0;
        crate::leanh::lean_inc_ref(v_cfgFile_363_);
        v_leanFile_367_ = l_System_FilePath_addExtension(v_cfgFile_363_, v___x_366_);
        v___x_368_ = l_System_FilePath_pathExists(v_leanFile_367_);
        crate::leanh::lean_dec_ref(v_leanFile_367_);
        if v___x_368_ == 0 {
            let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tomlFile_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_371_: u8 = 0;
            v___x_369_ = l_Lake_configFileExists___closed__1;
            v_tomlFile_370_ = l_System_FilePath_addExtension(v_cfgFile_363_, v___x_369_);
            v___x_371_ = l_System_FilePath_pathExists(v_tomlFile_370_);
            crate::leanh::lean_dec_ref(v_tomlFile_370_);
            return v___x_371_;
        } else {
            crate::leanh::lean_dec_ref(v_cfgFile_363_);
            return v___x_368_;
        }
    } else {
        let mut v___x_372_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_365_, 1);
        v___x_372_ = l_System_FilePath_pathExists(v_cfgFile_363_);
        crate::leanh::lean_dec_ref(v_cfgFile_363_);
        return v___x_372_;
    }
}
pub unsafe fn l_Lake_configFileExists___boxed(
    mut v_cfgFile_373_: *mut crate::leanh::LeanObject,
    mut v_a_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_375_: u8 = 0;
    let mut v_r_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_375_ = l_Lake_configFileExists(v_cfgFile_373_);
    v_r_376_ = crate::leanh::lean_box((v_res_375_) as usize);
    return v_r_376_;
}
pub unsafe fn l_Lake_realConfigFile(
    mut v_cfgFile_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_cfgFile_377_);
    v___x_379_ = l_System_FilePath_extension(v_cfgFile_377_);
    if crate::leanh::lean_obj_tag(v___x_379_) == 0 {
        let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_385_: u8 = 0;
        v___x_380_ = l_Lake_configFileExists___closed__0;
        crate::leanh::lean_inc_ref(v_cfgFile_377_);
        v___x_381_ = l_System_FilePath_addExtension(v_cfgFile_377_, v___x_380_);
        v___x_382_ = l_Lake_resolvePath(v___x_381_);
        v___x_383_ = lean_string_utf8_byte_size(v___x_382_);
        v___x_384_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_385_ = lean_nat_dec_eq(v___x_383_, v___x_384_);
        if v___x_385_ == 0 {
            crate::leanh::lean_dec_ref(v_cfgFile_377_);
            return v___x_382_;
        } else {
            let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_382_);
            v___x_386_ = l_Lake_configFileExists___closed__1;
            v___x_387_ = l_System_FilePath_addExtension(v_cfgFile_377_, v___x_386_);
            v___x_388_ = l_Lake_resolvePath(v___x_387_);
            return v___x_388_;
        }
    } else {
        let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_379_, 1);
        v___x_389_ = l_Lake_resolvePath(v_cfgFile_377_);
        return v___x_389_;
    }
}
pub unsafe fn l_Lake_realConfigFile___boxed(
    mut v_cfgFile_390_: *mut crate::leanh::LeanObject,
    mut v_a_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_392_ = l_Lake_realConfigFile(v_cfgFile_390_);
    return v_res_392_;
}
pub unsafe fn l_Lake_resolveConfigFile(
    mut v_name_406_: *mut crate::leanh::LeanObject,
    mut v_cfg_407_: *mut crate::leanh::LeanObject,
    mut v_a_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_configLang_x3f_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wsDir_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgIdx_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgName_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relPkgDir_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relConfigFile_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageOverrides_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeOpts_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reconfigure_424_: u8 = 0;
    let mut v_updateDeps_425_: u8 = 0;
    let mut v_updateToolchain_426_: u8 = 0;
    let mut v_scope_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remoteUrl_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_431_: u8 = 0;
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: u8 = 0;
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: u8 = 0;
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: u8 = 0;
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: u8 = 0;
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: u8 = 0;
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relLeanFile_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanFile_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relTomlFile_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tomlFile_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: u8 = 0;
    let mut v___x_478_: u8 = 0;
    let mut v___y_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: u8 = 0;
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_517_: u8 = 0;
    let mut v_unused_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wsDir_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgIdx_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgName_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relPkgDir_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgDir_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relConfigFile_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageOverrides_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeOpts_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOpts_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reconfigure_532_: u8 = 0;
    let mut v_updateDeps_533_: u8 = 0;
    let mut v_updateToolchain_534_: u8 = 0;
    let mut v_scope_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remoteUrl_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_539_: u8 = 0;
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_556_: u8 = 0;
    let mut v_unused_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_configLang_x3f_410_ = crate::leanh::lean_ctor_get(v_cfg_407_, 9);
                if crate::leanh::lean_obj_tag(v_configLang_x3f_410_) == 0 {
                    v_lakeEnv_411_ = crate::leanh::lean_ctor_get(v_cfg_407_, 0);
                    v_lakeArgs_x3f_412_ = crate::leanh::lean_ctor_get(v_cfg_407_, 1);
                    v_wsDir_413_ = crate::leanh::lean_ctor_get(v_cfg_407_, 2);
                    v_pkgIdx_414_ = crate::leanh::lean_ctor_get(v_cfg_407_, 3);
                    v_pkgName_415_ = crate::leanh::lean_ctor_get(v_cfg_407_, 4);
                    v_relPkgDir_416_ = crate::leanh::lean_ctor_get(v_cfg_407_, 5);
                    v_pkgDir_417_ = crate::leanh::lean_ctor_get(v_cfg_407_, 6);
                    v_relConfigFile_418_ = crate::leanh::lean_ctor_get(v_cfg_407_, 7);
                    v_configFile_419_ = crate::leanh::lean_ctor_get(v_cfg_407_, 8);
                    v_relManifestFile_420_ = crate::leanh::lean_ctor_get(v_cfg_407_, 10);
                    v_packageOverrides_421_ = crate::leanh::lean_ctor_get(v_cfg_407_, 11);
                    v_lakeOpts_422_ = crate::leanh::lean_ctor_get(v_cfg_407_, 12);
                    v_leanOpts_423_ = crate::leanh::lean_ctor_get(v_cfg_407_, 13);
                    v_reconfigure_424_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_407_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                    );
                    v_updateDeps_425_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_407_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                    );
                    v_updateToolchain_426_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_407_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                    );
                    v_scope_427_ = crate::leanh::lean_ctor_get(v_cfg_407_, 14);
                    v_remoteUrl_428_ = crate::leanh::lean_ctor_get(v_cfg_407_, 15);
                    v_isSharedCheck_517_ = (!crate::leanh::lean_is_exclusive(v_cfg_407_)) as u8;
                    if v_isSharedCheck_517_ == 0 {
                        v_unused_518_ = crate::leanh::lean_ctor_get(v_cfg_407_, 9);
                        crate::leanh::lean_dec(v_unused_518_);
                        v___x_430_ = v_cfg_407_;
                        v_isShared_431_ = v_isSharedCheck_517_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_remoteUrl_428_);
                        crate::leanh::lean_inc(v_scope_427_);
                        crate::leanh::lean_inc(v_leanOpts_423_);
                        crate::leanh::lean_inc(v_lakeOpts_422_);
                        crate::leanh::lean_inc(v_packageOverrides_421_);
                        crate::leanh::lean_inc(v_relManifestFile_420_);
                        crate::leanh::lean_inc(v_configFile_419_);
                        crate::leanh::lean_inc(v_relConfigFile_418_);
                        crate::leanh::lean_inc(v_pkgDir_417_);
                        crate::leanh::lean_inc(v_relPkgDir_416_);
                        crate::leanh::lean_inc(v_pkgName_415_);
                        crate::leanh::lean_inc(v_pkgIdx_414_);
                        crate::leanh::lean_inc(v_wsDir_413_);
                        crate::leanh::lean_inc(v_lakeArgs_x3f_412_);
                        crate::leanh::lean_inc(v_lakeEnv_411_);
                        crate::leanh::lean_dec(v_cfg_407_);
                        v___x_430_ = crate::leanh::lean_box(0);
                        v_isShared_431_ = v_isSharedCheck_517_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_configLang_x3f_410_);
                    v_lakeEnv_519_ = crate::leanh::lean_ctor_get(v_cfg_407_, 0);
                    v_lakeArgs_x3f_520_ = crate::leanh::lean_ctor_get(v_cfg_407_, 1);
                    v_wsDir_521_ = crate::leanh::lean_ctor_get(v_cfg_407_, 2);
                    v_pkgIdx_522_ = crate::leanh::lean_ctor_get(v_cfg_407_, 3);
                    v_pkgName_523_ = crate::leanh::lean_ctor_get(v_cfg_407_, 4);
                    v_relPkgDir_524_ = crate::leanh::lean_ctor_get(v_cfg_407_, 5);
                    v_pkgDir_525_ = crate::leanh::lean_ctor_get(v_cfg_407_, 6);
                    v_relConfigFile_526_ = crate::leanh::lean_ctor_get(v_cfg_407_, 7);
                    v_configFile_527_ = crate::leanh::lean_ctor_get(v_cfg_407_, 8);
                    v_relManifestFile_528_ = crate::leanh::lean_ctor_get(v_cfg_407_, 10);
                    v_packageOverrides_529_ = crate::leanh::lean_ctor_get(v_cfg_407_, 11);
                    v_lakeOpts_530_ = crate::leanh::lean_ctor_get(v_cfg_407_, 12);
                    v_leanOpts_531_ = crate::leanh::lean_ctor_get(v_cfg_407_, 13);
                    v_reconfigure_532_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_407_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                    );
                    v_updateDeps_533_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_407_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                    );
                    v_updateToolchain_534_ = crate::leanh::lean_ctor_get_uint8(
                        v_cfg_407_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                    );
                    v_scope_535_ = crate::leanh::lean_ctor_get(v_cfg_407_, 14);
                    v_remoteUrl_536_ = crate::leanh::lean_ctor_get(v_cfg_407_, 15);
                    v_isSharedCheck_556_ = (!crate::leanh::lean_is_exclusive(v_cfg_407_)) as u8;
                    if v_isSharedCheck_556_ == 0 {
                        v_unused_557_ = crate::leanh::lean_ctor_get(v_cfg_407_, 9);
                        crate::leanh::lean_dec(v_unused_557_);
                        v___x_538_ = v_cfg_407_;
                        v_isShared_539_ = v_isSharedCheck_556_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_remoteUrl_536_);
                        crate::leanh::lean_inc(v_scope_535_);
                        crate::leanh::lean_inc(v_leanOpts_531_);
                        crate::leanh::lean_inc(v_lakeOpts_530_);
                        crate::leanh::lean_inc(v_packageOverrides_529_);
                        crate::leanh::lean_inc(v_relManifestFile_528_);
                        crate::leanh::lean_inc(v_configFile_527_);
                        crate::leanh::lean_inc(v_relConfigFile_526_);
                        crate::leanh::lean_inc(v_pkgDir_525_);
                        crate::leanh::lean_inc(v_relPkgDir_524_);
                        crate::leanh::lean_inc(v_pkgName_523_);
                        crate::leanh::lean_inc(v_pkgIdx_522_);
                        crate::leanh::lean_inc(v_wsDir_521_);
                        crate::leanh::lean_inc(v_lakeArgs_x3f_520_);
                        crate::leanh::lean_inc(v_lakeEnv_519_);
                        crate::leanh::lean_dec(v_cfg_407_);
                        v___x_538_ = crate::leanh::lean_box(0);
                        v_isShared_539_ = v_isSharedCheck_556_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_relConfigFile_418_);
                v___x_432_ = l_System_FilePath_extension(v_relConfigFile_418_);
                if crate::leanh::lean_obj_tag(v___x_432_) == 1 {
                    v_val_433_ = crate::leanh::lean_ctor_get(v___x_432_, 0);
                    crate::leanh::lean_inc(v_val_433_);
                    crate::leanh::lean_dec_ref_known(v___x_432_, 1);
                    crate::leanh::lean_inc_ref(v_configFile_419_);
                    v___x_434_ = l_Lake_resolvePath(v_configFile_419_);
                    v___x_435_ = lean_string_utf8_byte_size(v___x_434_);
                    v___x_436_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_437_ = lean_nat_dec_eq(v___x_435_, v___x_436_);
                    if v___x_437_ == 0 {
                        crate::leanh::lean_dec_ref(v_configFile_419_);
                        v___x_438_ = l_Lake_configFileExists___closed__0;
                        v___x_439_ = lean_string_dec_eq(v_val_433_, v___x_438_);
                        if v___x_439_ == 0 {
                            v___x_440_ = l_Lake_configFileExists___closed__1;
                            v___x_441_ = lean_string_dec_eq(v_val_433_, v___x_440_);
                            crate::leanh::lean_dec(v_val_433_);
                            if v___x_441_ == 0 {
                                crate::leanh::lean_del_object(v___x_430_);
                                crate::leanh::lean_dec_ref(v_remoteUrl_428_);
                                crate::leanh::lean_dec_ref(v_scope_427_);
                                crate::leanh::lean_dec_ref(v_leanOpts_423_);
                                crate::leanh::lean_dec(v_lakeOpts_422_);
                                crate::leanh::lean_dec_ref(v_packageOverrides_421_);
                                crate::leanh::lean_dec_ref(v_relManifestFile_420_);
                                crate::leanh::lean_dec_ref(v_relConfigFile_418_);
                                crate::leanh::lean_dec_ref(v_pkgDir_417_);
                                crate::leanh::lean_dec_ref(v_relPkgDir_416_);
                                crate::leanh::lean_dec(v_pkgName_415_);
                                crate::leanh::lean_dec(v_pkgIdx_414_);
                                crate::leanh::lean_dec_ref(v_wsDir_413_);
                                crate::leanh::lean_dec(v_lakeArgs_x3f_412_);
                                crate::leanh::lean_dec_ref(v_lakeEnv_411_);
                                v___x_442_ = l_Lake_resolveConfigFile___closed__0;
                                v___x_443_ = lean_string_append(v_name_406_, v___x_442_);
                                v___x_444_ = lean_string_append(v___x_443_, v___x_434_);
                                crate::leanh::lean_dec_ref(v___x_434_);
                                v___x_445_ = 3;
                                v___x_446_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_446_, 0, v___x_444_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_446_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_445_,
                                );
                                v___x_447_ = lean_array_get_size(v_a_408_);
                                v___x_448_ = lean_array_push(v_a_408_, v___x_446_);
                                v___x_449_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_449_, 0, v___x_447_);
                                crate::leanh::lean_ctor_set(v___x_449_, 1, v___x_448_);
                                return v___x_449_;
                            } else {
                                crate::leanh::lean_dec_ref(v_name_406_);
                                v___x_450_ = l_Lake_resolveConfigFile___closed__1;
                                if v_isShared_431_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_430_, 9, v___x_450_);
                                    crate::leanh::lean_ctor_set(v___x_430_, 8, v___x_434_);
                                    v___x_452_ = v___x_430_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_454_ =
                                        crate::leanh::lean_alloc_ctor(0, 16, (3) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        0,
                                        v_lakeEnv_411_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        1,
                                        v_lakeArgs_x3f_412_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        2,
                                        v_wsDir_413_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        3,
                                        v_pkgIdx_414_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        4,
                                        v_pkgName_415_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        5,
                                        v_relPkgDir_416_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        6,
                                        v_pkgDir_417_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        7,
                                        v_relConfigFile_418_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        8,
                                        v___x_434_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        9,
                                        v___x_450_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        10,
                                        v_relManifestFile_420_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        11,
                                        v_packageOverrides_421_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        12,
                                        v_lakeOpts_422_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        13,
                                        v_leanOpts_423_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        14,
                                        v_scope_427_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_454_,
                                        15,
                                        v_remoteUrl_428_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v_reuseFailAlloc_454_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16)
                                            as u32,
                                        v_reconfigure_424_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v_reuseFailAlloc_454_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16
                                            + 1) as u32,
                                        v_updateDeps_425_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v_reuseFailAlloc_454_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16
                                            + 2) as u32,
                                        v_updateToolchain_426_,
                                    );
                                    v___x_452_ = v_reuseFailAlloc_454_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_433_);
                            crate::leanh::lean_dec_ref(v_name_406_);
                            v___x_455_ = l_Lake_resolveConfigFile___closed__2;
                            if v_isShared_431_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_430_, 9, v___x_455_);
                                crate::leanh::lean_ctor_set(v___x_430_, 8, v___x_434_);
                                v___x_457_ = v___x_430_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_459_ =
                                    crate::leanh::lean_alloc_ctor(0, 16, (3) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    0,
                                    v_lakeEnv_411_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    1,
                                    v_lakeArgs_x3f_412_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 2, v_wsDir_413_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    3,
                                    v_pkgIdx_414_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    4,
                                    v_pkgName_415_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    5,
                                    v_relPkgDir_416_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    6,
                                    v_pkgDir_417_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    7,
                                    v_relConfigFile_418_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 8, v___x_434_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 9, v___x_455_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    10,
                                    v_relManifestFile_420_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    11,
                                    v_packageOverrides_421_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    12,
                                    v_lakeOpts_422_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    13,
                                    v_leanOpts_423_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    14,
                                    v_scope_427_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_459_,
                                    15,
                                    v_remoteUrl_428_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_459_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16)
                                        as u32,
                                    v_reconfigure_424_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_459_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1)
                                        as u32,
                                    v_updateDeps_425_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_459_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2)
                                        as u32,
                                    v_updateToolchain_426_,
                                );
                                v___x_457_ = v_reuseFailAlloc_459_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_434_);
                        crate::leanh::lean_dec(v_val_433_);
                        crate::leanh::lean_del_object(v___x_430_);
                        crate::leanh::lean_dec_ref(v_remoteUrl_428_);
                        crate::leanh::lean_dec_ref(v_scope_427_);
                        crate::leanh::lean_dec_ref(v_leanOpts_423_);
                        crate::leanh::lean_dec(v_lakeOpts_422_);
                        crate::leanh::lean_dec_ref(v_packageOverrides_421_);
                        crate::leanh::lean_dec_ref(v_relManifestFile_420_);
                        crate::leanh::lean_dec_ref(v_relConfigFile_418_);
                        crate::leanh::lean_dec_ref(v_pkgDir_417_);
                        crate::leanh::lean_dec_ref(v_relPkgDir_416_);
                        crate::leanh::lean_dec(v_pkgName_415_);
                        crate::leanh::lean_dec(v_pkgIdx_414_);
                        crate::leanh::lean_dec_ref(v_wsDir_413_);
                        crate::leanh::lean_dec(v_lakeArgs_x3f_412_);
                        crate::leanh::lean_dec_ref(v_lakeEnv_411_);
                        v___x_460_ = l_Lake_resolveConfigFile___closed__3;
                        v___x_461_ = lean_string_append(v_name_406_, v___x_460_);
                        v___x_462_ = lean_string_append(v___x_461_, v_configFile_419_);
                        crate::leanh::lean_dec_ref(v_configFile_419_);
                        v___x_463_ = 3;
                        v___x_464_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_464_, 0, v___x_462_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_464_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_463_,
                        );
                        v___x_465_ = lean_array_get_size(v_a_408_);
                        v___x_466_ = lean_array_push(v_a_408_, v___x_464_);
                        v___x_467_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_467_, 0, v___x_465_);
                        crate::leanh::lean_ctor_set(v___x_467_, 1, v___x_466_);
                        return v___x_467_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_432_);
                    crate::leanh::lean_dec_ref(v_configFile_419_);
                    v___x_468_ = l_Lake_configFileExists___closed__0;
                    crate::leanh::lean_inc_ref(v_relConfigFile_418_);
                    v_relLeanFile_469_ =
                        l_System_FilePath_addExtension(v_relConfigFile_418_, v___x_468_);
                    crate::leanh::lean_inc_ref(v_relLeanFile_469_);
                    crate::leanh::lean_inc_ref_n(v_pkgDir_417_, 2);
                    v_leanFile_470_ = l_Lake_joinRelative(v_pkgDir_417_, v_relLeanFile_469_);
                    crate::leanh::lean_inc_ref(v_leanFile_470_);
                    v___x_471_ = l_Lake_resolvePath(v_leanFile_470_);
                    v___x_472_ = l_Lake_configFileExists___closed__1;
                    v_relTomlFile_473_ =
                        l_System_FilePath_addExtension(v_relConfigFile_418_, v___x_472_);
                    crate::leanh::lean_inc_ref(v_relTomlFile_473_);
                    v_tomlFile_474_ = l_Lake_joinRelative(v_pkgDir_417_, v_relTomlFile_473_);
                    v___x_475_ = lean_string_utf8_byte_size(v___x_471_);
                    v___x_476_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_477_ = lean_nat_dec_eq(v___x_475_, v___x_476_);
                    if v___x_477_ == 0 {
                        crate::leanh::lean_dec_ref(v_leanFile_470_);
                        v___x_478_ = l_System_FilePath_pathExists(v_tomlFile_474_);
                        crate::leanh::lean_dec_ref(v_tomlFile_474_);
                        if v___x_478_ == 0 {
                            crate::leanh::lean_dec_ref(v_relTomlFile_473_);
                            crate::leanh::lean_dec_ref(v_name_406_);
                            v___y_480_ = v_a_408_;
                            state = 4;
                            continue;
                        } else {
                            v___x_486_ = l_Lake_resolveConfigFile___closed__4;
                            v___x_487_ = lean_string_append(v_name_406_, v___x_486_);
                            v___x_488_ = lean_string_append(v___x_487_, v_relLeanFile_469_);
                            v___x_489_ = l_Lake_resolveConfigFile___closed__5;
                            v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
                            v___x_491_ = lean_string_append(v___x_490_, v_relTomlFile_473_);
                            crate::leanh::lean_dec_ref(v_relTomlFile_473_);
                            v___x_492_ = l_Lake_resolveConfigFile___closed__6;
                            v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
                            v___x_494_ = lean_string_append(v___x_493_, v_relLeanFile_469_);
                            v___x_495_ = 1;
                            v___x_496_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_496_, 0, v___x_494_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_496_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_495_,
                            );
                            v___x_497_ = lean_array_push(v_a_408_, v___x_496_);
                            v___y_480_ = v___x_497_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_471_);
                        crate::leanh::lean_dec_ref(v_relLeanFile_469_);
                        crate::leanh::lean_inc_ref(v_tomlFile_474_);
                        v___x_498_ = l_Lake_resolvePath(v_tomlFile_474_);
                        v___x_499_ = lean_string_utf8_byte_size(v___x_498_);
                        v___x_500_ = lean_nat_dec_eq(v___x_499_, v___x_476_);
                        if v___x_500_ == 0 {
                            crate::leanh::lean_dec_ref(v_tomlFile_474_);
                            crate::leanh::lean_dec_ref(v_leanFile_470_);
                            crate::leanh::lean_dec_ref(v_name_406_);
                            v___x_501_ = l_Lake_resolveConfigFile___closed__1;
                            if v_isShared_431_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_430_, 9, v___x_501_);
                                crate::leanh::lean_ctor_set(v___x_430_, 8, v___x_498_);
                                crate::leanh::lean_ctor_set(v___x_430_, 7, v_relTomlFile_473_);
                                v___x_503_ = v___x_430_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_505_ =
                                    crate::leanh::lean_alloc_ctor(0, 16, (3) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    0,
                                    v_lakeEnv_411_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    1,
                                    v_lakeArgs_x3f_412_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_505_, 2, v_wsDir_413_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    3,
                                    v_pkgIdx_414_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    4,
                                    v_pkgName_415_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    5,
                                    v_relPkgDir_416_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    6,
                                    v_pkgDir_417_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    7,
                                    v_relTomlFile_473_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_505_, 8, v___x_498_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_505_, 9, v___x_501_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    10,
                                    v_relManifestFile_420_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    11,
                                    v_packageOverrides_421_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    12,
                                    v_lakeOpts_422_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    13,
                                    v_leanOpts_423_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    14,
                                    v_scope_427_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_505_,
                                    15,
                                    v_remoteUrl_428_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_505_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16)
                                        as u32,
                                    v_reconfigure_424_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_505_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1)
                                        as u32,
                                    v_updateDeps_425_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_505_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2)
                                        as u32,
                                    v_updateToolchain_426_,
                                );
                                v___x_503_ = v_reuseFailAlloc_505_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_498_);
                            crate::leanh::lean_dec_ref(v_relTomlFile_473_);
                            crate::leanh::lean_del_object(v___x_430_);
                            crate::leanh::lean_dec_ref(v_remoteUrl_428_);
                            crate::leanh::lean_dec_ref(v_scope_427_);
                            crate::leanh::lean_dec_ref(v_leanOpts_423_);
                            crate::leanh::lean_dec(v_lakeOpts_422_);
                            crate::leanh::lean_dec_ref(v_packageOverrides_421_);
                            crate::leanh::lean_dec_ref(v_relManifestFile_420_);
                            crate::leanh::lean_dec_ref(v_pkgDir_417_);
                            crate::leanh::lean_dec_ref(v_relPkgDir_416_);
                            crate::leanh::lean_dec(v_pkgName_415_);
                            crate::leanh::lean_dec(v_pkgIdx_414_);
                            crate::leanh::lean_dec_ref(v_wsDir_413_);
                            crate::leanh::lean_dec(v_lakeArgs_x3f_412_);
                            crate::leanh::lean_dec_ref(v_lakeEnv_411_);
                            v___x_506_ = l_Lake_resolveConfigFile___closed__7;
                            v___x_507_ = lean_string_append(v_name_406_, v___x_506_);
                            v___x_508_ = lean_string_append(v___x_507_, v_leanFile_470_);
                            crate::leanh::lean_dec_ref(v_leanFile_470_);
                            v___x_509_ = l_Lake_resolveConfigFile___closed__8;
                            v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
                            v___x_511_ = lean_string_append(v___x_510_, v_tomlFile_474_);
                            crate::leanh::lean_dec_ref(v_tomlFile_474_);
                            v___x_512_ = 3;
                            v___x_513_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_513_, 0, v___x_511_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_513_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_512_,
                            );
                            v___x_514_ = lean_array_get_size(v_a_408_);
                            v___x_515_ = lean_array_push(v_a_408_, v___x_513_);
                            v___x_516_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_516_, 0, v___x_514_);
                            crate::leanh::lean_ctor_set(v___x_516_, 1, v___x_515_);
                            return v___x_516_;
                        }
                    }
                }
            }
            2 => {
                v___x_453_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_453_, 0, v___x_452_);
                crate::leanh::lean_ctor_set(v___x_453_, 1, v_a_408_);
                return v___x_453_;
            }
            3 => {
                v___x_458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_458_, 0, v___x_457_);
                crate::leanh::lean_ctor_set(v___x_458_, 1, v_a_408_);
                return v___x_458_;
            }
            4 => {
                v___x_481_ = l_Lake_resolveConfigFile___closed__2;
                if v_isShared_431_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_430_, 9, v___x_481_);
                    crate::leanh::lean_ctor_set(v___x_430_, 8, v___x_471_);
                    crate::leanh::lean_ctor_set(v___x_430_, 7, v_relLeanFile_469_);
                    v___x_483_ = v___x_430_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_485_ = crate::leanh::lean_alloc_ctor(0, 16, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 0, v_lakeEnv_411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 1, v_lakeArgs_x3f_412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 2, v_wsDir_413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 3, v_pkgIdx_414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 4, v_pkgName_415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 5, v_relPkgDir_416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 6, v_pkgDir_417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 7, v_relLeanFile_469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 8, v___x_471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 9, v___x_481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 10, v_relManifestFile_420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 11, v_packageOverrides_421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 12, v_lakeOpts_422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 13, v_leanOpts_423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 14, v_scope_427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 15, v_remoteUrl_428_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_485_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                        v_reconfigure_424_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_485_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                        v_updateDeps_425_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_485_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                        v_updateToolchain_426_,
                    );
                    v___x_483_ = v_reuseFailAlloc_485_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_484_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_484_, 0, v___x_483_);
                crate::leanh::lean_ctor_set(v___x_484_, 1, v___y_480_);
                return v___x_484_;
            }
            6 => {
                v___x_504_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_504_, 0, v___x_503_);
                crate::leanh::lean_ctor_set(v___x_504_, 1, v_a_408_);
                return v___x_504_;
            }
            7 => {
                crate::leanh::lean_inc_ref(v_configFile_527_);
                v___x_540_ = l_Lake_resolvePath(v_configFile_527_);
                v___x_541_ = lean_string_utf8_byte_size(v___x_540_);
                v___x_542_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_543_ = lean_nat_dec_eq(v___x_541_, v___x_542_);
                if v___x_543_ == 0 {
                    crate::leanh::lean_dec_ref(v_configFile_527_);
                    crate::leanh::lean_dec_ref(v_name_406_);
                    if v_isShared_539_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_538_, 8, v___x_540_);
                        v___x_545_ = v___x_538_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_547_ = crate::leanh::lean_alloc_ctor(0, 16, (3) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 0, v_lakeEnv_519_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 1, v_lakeArgs_x3f_520_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 2, v_wsDir_521_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 3, v_pkgIdx_522_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 4, v_pkgName_523_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 5, v_relPkgDir_524_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 6, v_pkgDir_525_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 7, v_relConfigFile_526_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 8, v___x_540_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_547_,
                            9,
                            v_configLang_x3f_410_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_547_,
                            10,
                            v_relManifestFile_528_,
                        );
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_547_,
                            11,
                            v_packageOverrides_529_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 12, v_lakeOpts_530_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 13, v_leanOpts_531_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 14, v_scope_535_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 15, v_remoteUrl_536_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_547_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                            v_reconfigure_532_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_547_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                            v_updateDeps_533_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_547_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                            v_updateToolchain_534_,
                        );
                        v___x_545_ = v_reuseFailAlloc_547_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_540_);
                    crate::leanh::lean_del_object(v___x_538_);
                    crate::leanh::lean_dec_ref(v_remoteUrl_536_);
                    crate::leanh::lean_dec_ref(v_scope_535_);
                    crate::leanh::lean_dec_ref(v_leanOpts_531_);
                    crate::leanh::lean_dec(v_lakeOpts_530_);
                    crate::leanh::lean_dec_ref(v_packageOverrides_529_);
                    crate::leanh::lean_dec_ref(v_relManifestFile_528_);
                    crate::leanh::lean_dec_ref(v_relConfigFile_526_);
                    crate::leanh::lean_dec_ref(v_pkgDir_525_);
                    crate::leanh::lean_dec_ref(v_relPkgDir_524_);
                    crate::leanh::lean_dec(v_pkgName_523_);
                    crate::leanh::lean_dec(v_pkgIdx_522_);
                    crate::leanh::lean_dec_ref(v_wsDir_521_);
                    crate::leanh::lean_dec(v_lakeArgs_x3f_520_);
                    crate::leanh::lean_dec_ref_known(v_configLang_x3f_410_, 1);
                    crate::leanh::lean_dec_ref(v_lakeEnv_519_);
                    v___x_548_ = l_Lake_resolveConfigFile___closed__3;
                    v___x_549_ = lean_string_append(v_name_406_, v___x_548_);
                    v___x_550_ = lean_string_append(v___x_549_, v_configFile_527_);
                    crate::leanh::lean_dec_ref(v_configFile_527_);
                    v___x_551_ = 3;
                    v___x_552_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_552_, 0, v___x_550_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_552_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_551_,
                    );
                    v___x_553_ = lean_array_get_size(v_a_408_);
                    v___x_554_ = lean_array_push(v_a_408_, v___x_552_);
                    v___x_555_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_555_, 0, v___x_553_);
                    crate::leanh::lean_ctor_set(v___x_555_, 1, v___x_554_);
                    return v___x_555_;
                }
            }
            8 => {
                v___x_546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_546_, 0, v___x_545_);
                crate::leanh::lean_ctor_set(v___x_546_, 1, v_a_408_);
                return v___x_546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_resolveConfigFile___boxed(
    mut v_name_558_: *mut crate::leanh::LeanObject,
    mut v_cfg_559_: *mut crate::leanh::LeanObject,
    mut v_a_560_: *mut crate::leanh::LeanObject,
    mut v_a_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Lake_resolveConfigFile(v_name_558_, v_cfg_559_, v_a_560_);
    return v_res_562_;
}
pub unsafe fn l_Lake_loadConfigFile___redArg(
    mut v_cfg_563_: *mut crate::leanh::LeanObject,
    mut v_a_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_configLang_x3f_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: u8 = 0;
    v_configLang_x3f_566_ = crate::leanh::lean_ctor_get(v_cfg_563_, 9);
    v_val_567_ = crate::leanh::lean_ctor_get(v_configLang_x3f_566_, 0);
    v___x_568_ = (crate::leanh::lean_unbox(v_val_567_) as u8);
    if v___x_568_ == 0 {
        let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_569_ = l_Lake_loadLeanConfig(v_cfg_563_, v_a_564_);
        return v___x_569_;
    } else {
        let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_570_ = l_Lake_loadTomlConfig(v_cfg_563_, v_a_564_);
        return v___x_570_;
    }
}
pub unsafe fn l_Lake_loadConfigFile___redArg___boxed(
    mut v_cfg_571_: *mut crate::leanh::LeanObject,
    mut v_a_572_: *mut crate::leanh::LeanObject,
    mut v_a_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lake_loadConfigFile___redArg(v_cfg_571_, v_a_572_);
    return v_res_574_;
}
pub unsafe fn l_Lake_loadConfigFile(
    mut v_cfg_575_: *mut crate::leanh::LeanObject,
    mut v_h_576_: *mut crate::leanh::LeanObject,
    mut v_a_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ = l_Lake_loadConfigFile___redArg(v_cfg_575_, v_a_577_);
    return v___x_579_;
}
pub unsafe fn l_Lake_loadConfigFile___boxed(
    mut v_cfg_580_: *mut crate::leanh::LeanObject,
    mut v_h_581_: *mut crate::leanh::LeanObject,
    mut v_a_582_: *mut crate::leanh::LeanObject,
    mut v_a_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lake_loadConfigFile(v_cfg_580_, v_h_581_, v_a_582_);
    return v_res_584_;
}
pub unsafe fn l_Lake_loadPackage(
    mut v_cfg_586_: *mut crate::leanh::LeanObject,
    mut v_a_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lakeEnv_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_602_: u8 = 0;
    let mut v_pkgIdx_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_608_: u8 = 0;
    let mut v_a_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_613_: u8 = 0;
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v_a_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_622_: u8 = 0;
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_589_ = crate::leanh::lean_ctor_get(v_cfg_586_, 0);
                v___x_590_ = l_Lean_searchPathRef;
                v___x_591_ = l_Lake_Env_leanSearchPath(v_lakeEnv_589_);
                v___x_592_ = lean_st_ref_set(v___x_590_, v___x_591_);
                v___x_593_ = l_Lake_loadPackage___closed__0;
                v___x_594_ = l_Lake_resolveConfigFile(v___x_593_, v_cfg_586_, v_a_587_);
                if crate::leanh::lean_obj_tag(v___x_594_) == 0 {
                    v_a_595_ = crate::leanh::lean_ctor_get(v___x_594_, 0);
                    crate::leanh::lean_inc_n(v_a_595_, 2);
                    v_a_596_ = crate::leanh::lean_ctor_get(v___x_594_, 1);
                    crate::leanh::lean_inc(v_a_596_);
                    crate::leanh::lean_dec_ref_known(v___x_594_, 2);
                    v___x_597_ = l_Lake_loadConfigFile___redArg(v_a_595_, v_a_596_);
                    if crate::leanh::lean_obj_tag(v___x_597_) == 0 {
                        v_a_598_ = crate::leanh::lean_ctor_get(v___x_597_, 0);
                        v_a_599_ = crate::leanh::lean_ctor_get(v___x_597_, 1);
                        v_isSharedCheck_608_ = (!crate::leanh::lean_is_exclusive(v___x_597_)) as u8;
                        if v_isSharedCheck_608_ == 0 {
                            v___x_601_ = v___x_597_;
                            v_isShared_602_ = v_isSharedCheck_608_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_599_);
                            crate::leanh::lean_inc(v_a_598_);
                            crate::leanh::lean_dec(v___x_597_);
                            v___x_601_ = crate::leanh::lean_box(0);
                            v_isShared_602_ = v_isSharedCheck_608_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_595_);
                        v_a_609_ = crate::leanh::lean_ctor_get(v___x_597_, 0);
                        v_a_610_ = crate::leanh::lean_ctor_get(v___x_597_, 1);
                        v_isSharedCheck_617_ = (!crate::leanh::lean_is_exclusive(v___x_597_)) as u8;
                        if v_isSharedCheck_617_ == 0 {
                            v___x_612_ = v___x_597_;
                            v_isShared_613_ = v_isSharedCheck_617_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_610_);
                            crate::leanh::lean_inc(v_a_609_);
                            crate::leanh::lean_dec(v___x_597_);
                            v___x_612_ = crate::leanh::lean_box(0);
                            v_isShared_613_ = v_isSharedCheck_617_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_618_ = crate::leanh::lean_ctor_get(v___x_594_, 0);
                    v_a_619_ = crate::leanh::lean_ctor_get(v___x_594_, 1);
                    v_isSharedCheck_626_ = (!crate::leanh::lean_is_exclusive(v___x_594_)) as u8;
                    if v_isSharedCheck_626_ == 0 {
                        v___x_621_ = v___x_594_;
                        v_isShared_622_ = v_isSharedCheck_626_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_619_);
                        crate::leanh::lean_inc(v_a_618_);
                        crate::leanh::lean_dec(v___x_594_);
                        v___x_621_ = crate::leanh::lean_box(0);
                        v_isShared_622_ = v_isSharedCheck_626_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_pkgIdx_603_ = crate::leanh::lean_ctor_get(v_a_595_, 3);
                crate::leanh::lean_inc(v_pkgIdx_603_);
                v___x_604_ = l_Lake_mkPackage(v_a_595_, v_a_598_, v_pkgIdx_603_);
                crate::leanh::lean_dec(v_a_595_);
                if v_isShared_602_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_601_, 0, v___x_604_);
                    v___x_606_ = v___x_601_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_607_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_607_, 1, v_a_599_);
                    v___x_606_ = v_reuseFailAlloc_607_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_606_;
            }
            3 => {
                if v_isShared_613_ == 0 {
                    v___x_615_ = v___x_612_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 1, v_a_610_);
                    v___x_615_ = v_reuseFailAlloc_616_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_615_;
            }
            5 => {
                if v_isShared_622_ == 0 {
                    v___x_624_ = v___x_621_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_625_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_625_, 1, v_a_619_);
                    v___x_624_ = v_reuseFailAlloc_625_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_loadPackage___boxed(
    mut v_cfg_627_: *mut crate::leanh::LeanObject,
    mut v_a_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_630_ = l_Lake_loadPackage(v_cfg_627_, v_a_628_);
    return v_res_630_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Load_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LakefileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Toml(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Load_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LakefileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Lean(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Toml(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Load_Package(builtin);
}
