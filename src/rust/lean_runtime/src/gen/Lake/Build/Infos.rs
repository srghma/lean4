// Lean compiler output
// Module: Lake.Build.Infos
// Imports: Lake.Build.Info Lake.Config.LeanExe Lake.Config.ExternLib Lake.Config.InputFile Lake.Build.Data
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lake::Build::Data::{
    initialize_Lake_Build_Data, runtime_initialize_Lake_Build_Data,
};
use crate::r#gen::Lake::Build::Facets::{
    l_Lake_ExternLib_dynlibFacet, l_Lake_ExternLib_sharedFacet, l_Lake_ExternLib_staticFacet,
    l_Lake_InputDir_defaultFacet, l_Lake_InputFile_defaultFacet, l_Lake_LeanExe_exeFacet,
    l_Lake_LeanLib_defaultFacet, l_Lake_LeanLib_extraDepFacet, l_Lake_LeanLib_leanArtsFacet,
    l_Lake_LeanLib_sharedFacet, l_Lake_LeanLib_staticExportFacet, l_Lake_LeanLib_staticFacet,
    l_Lake_Module_bcFacet, l_Lake_Module_bcoFacet, l_Lake_Module_cFacet,
    l_Lake_Module_coExportFacet, l_Lake_Module_coFacet, l_Lake_Module_coNoExportFacet,
    l_Lake_Module_depsFacet, l_Lake_Module_exportInfoFacet, l_Lake_Module_headerFacet,
    l_Lake_Module_ileanFacet, l_Lake_Module_importAllArtsFacet, l_Lake_Module_importArtsFacet,
    l_Lake_Module_importInfoFacet, l_Lake_Module_irFacet, l_Lake_Module_leanArtsFacet,
    l_Lake_Module_leanFacet, l_Lake_Module_ltarFacet, l_Lake_Module_oExportFacet,
    l_Lake_Module_oFacet, l_Lake_Module_oNoExportFacet, l_Lake_Module_oleanFacet,
    l_Lake_Module_oleanPrivateFacet, l_Lake_Module_oleanServerFacet, l_Lake_Module_setupFacet,
    l_Lake_Package_buildCacheFacet, l_Lake_Package_extraDepFacet,
    l_Lake_Package_gitHubReleaseFacet, l_Lake_Package_optBuildCacheFacet,
    l_Lake_Package_optGitHubReleaseFacet, l_Lake_Package_optReservoirBarrelFacet,
    l_Lake_Package_reservoirBarrelFacet,
};
use crate::r#gen::Lake::Build::Info::{
    initialize_Lake_Build_Info, runtime_initialize_Lake_Build_Info,
};
use crate::r#gen::Lake::Config::ExternLib::{
    initialize_Lake_Config_ExternLib, runtime_initialize_Lake_Config_ExternLib,
};
use crate::r#gen::Lake::Config::InputFile::{
    initialize_Lake_Config_InputFile, runtime_initialize_Lake_Config_InputFile,
};
use crate::r#gen::Lake::Config::Kinds::{
    l_Lake_ExternLib_keyword, l_Lake_InputDir_keyword, l_Lake_InputFile_keyword,
    l_Lake_LeanExe_keyword, l_Lake_Module_keyword, l_Lake_Package_keyword,
};
use crate::r#gen::Lake::Config::LeanExe::{
    initialize_Lake_Config_LeanExe, runtime_initialize_Lake_Config_LeanExe,
};
pub static l_Lake_instDataKindModule___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lake_instDataKindModule___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindModule___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindModule___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindModule: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindPackage___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 97, 99, 107, 97, 103, 101, 0],
    };
static mut l_Lake_instDataKindPackage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindPackage___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6671755061125946191 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindPackage___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindPackage: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindLeanLib___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_instDataKindLeanLib___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindLeanLib___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindLeanLib___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindLeanLib: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindLeanExe___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 101, 97, 110, 95, 101, 120, 101, 0],
    };
static mut l_Lake_instDataKindLeanExe___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindLeanExe___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10587356296225942211 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindLeanExe___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindLeanExe: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindExternLib___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [101, 120, 116, 101, 114, 110, 95, 108, 105, 98, 0],
    };
static mut l_Lake_instDataKindExternLib___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindExternLib___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11562366611225967008 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindExternLib___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindExternLib: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindInputFile___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 112, 117, 116, 95, 102, 105, 108, 101, 0],
    };
static mut l_Lake_instDataKindInputFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindInputFile___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4067501922346325234 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindInputFile___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindInputFile: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindInputDir___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 0],
    };
static mut l_Lake_instDataKindInputDir___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instDataKindInputDir___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9710019104504222840 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindInputDir___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instDataKindInputDir: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_inputFacet___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 110, 112, 117, 116, 0],
    };
static mut l_Lake_Module_inputFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_inputFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_inputFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14553655559741226012 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_inputFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_inputFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_importsFacet___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [105, 109, 112, 111, 114, 116, 115, 0],
    };
static mut l_Lake_Module_importsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_importsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_importsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6906776088522269727 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_importsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_importsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_transImportsFacet___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [116, 114, 97, 110, 115, 73, 109, 112, 111, 114, 116, 115, 0],
    };
static mut l_Lake_Module_transImportsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_transImportsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_transImportsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15145167986846249592 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_transImportsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_transImportsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_precompileImportsFacet___closed__0_value: crate::leanh::LeanStringObject<
    18,
> = crate::leanh::LeanStringObject {
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
        112, 114, 101, 99, 111, 109, 112, 105, 108, 101, 73, 109, 112, 111, 114, 116, 115, 0,
    ],
};
static mut l_Lake_Module_precompileImportsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_precompileImportsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5134674735115079031 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_Module_precompileImportsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9286526061556025856 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_precompileImportsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_precompileImportsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_dynlibFacet___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [100, 121, 110, 108, 105, 98, 0],
    };
static mut l_Lake_Module_dynlibFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_dynlibFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_dynlibFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18425581243965226140 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_dynlibFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_dynlibFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLib_modulesFacet___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [109, 111, 100, 117, 108, 101, 115, 0],
    };
static mut l_Lake_LeanLib_modulesFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_LeanLib_modulesFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanLib_modulesFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15633005100005579590 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_modulesFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanLib_modulesFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_depsFacet___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [100, 101, 112, 115, 0],
    };
static mut l_Lake_Package_depsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_depsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6671755061125946191 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Package_depsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8196140624318363255 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_depsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_depsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_transDepsFacet___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 114, 97, 110, 115, 68, 101, 112, 115, 0],
    };
static mut l_Lake_Package_transDepsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_transDepsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6671755061125946191 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Package_transDepsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15594444263647844606 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_transDepsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_transDepsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_Module_key(
    mut v_self_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_643_: u8 = 0;
    let mut v_keyName_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut v_unused_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_638_ = crate::leanh::lean_ctor_get(v_self_637_, 0);
                v_pkg_639_ = crate::leanh::lean_ctor_get(v_lib_638_, 0);
                crate::leanh::lean_inc_ref(v_pkg_639_);
                v_name_640_ = crate::leanh::lean_ctor_get(v_self_637_, 1);
                v_isSharedCheck_648_ = (!crate::leanh::lean_is_exclusive(v_self_637_)) as u8;
                if v_isSharedCheck_648_ == 0 {
                    v_unused_649_ = crate::leanh::lean_ctor_get(v_self_637_, 0);
                    crate::leanh::lean_dec(v_unused_649_);
                    v___x_642_ = v_self_637_;
                    v_isShared_643_ = v_isSharedCheck_648_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_640_);
                    crate::leanh::lean_dec(v_self_637_);
                    v___x_642_ = crate::leanh::lean_box(0);
                    v_isShared_643_ = v_isSharedCheck_648_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_keyName_644_ = crate::leanh::lean_ctor_get(v_pkg_639_, 2);
                crate::leanh::lean_inc(v_keyName_644_);
                crate::leanh::lean_dec_ref(v_pkg_639_);
                if v_isShared_643_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_642_, 2);
                    crate::leanh::lean_ctor_set(v___x_642_, 0, v_keyName_644_);
                    v___x_646_ = v___x_642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_647_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_647_, 0, v_keyName_644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_647_, 1, v_name_640_);
                    v___x_646_ = v_reuseFailAlloc_647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ConfigTarget_key___redArg(
    mut v_self_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_651_ = crate::leanh::lean_ctor_get(v_self_650_, 0);
    v_name_652_ = crate::leanh::lean_ctor_get(v_self_650_, 1);
    v_keyName_653_ = crate::leanh::lean_ctor_get(v_pkg_651_, 2);
    crate::leanh::lean_inc(v_name_652_);
    crate::leanh::lean_inc(v_keyName_653_);
    v___x_654_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_654_, 0, v_keyName_653_);
    crate::leanh::lean_ctor_set(v___x_654_, 1, v_name_652_);
    return v___x_654_;
}
pub unsafe fn l_Lake_ConfigTarget_key___redArg___boxed(
    mut v_self_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_656_ = l_Lake_ConfigTarget_key___redArg(v_self_655_);
    crate::leanh::lean_dec_ref(v_self_655_);
    return v_res_656_;
}
pub unsafe fn l_Lake_ConfigTarget_key(
    mut v_kind_657_: *mut crate::leanh::LeanObject,
    mut v_self_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_659_ = crate::leanh::lean_ctor_get(v_self_658_, 0);
    v_name_660_ = crate::leanh::lean_ctor_get(v_self_658_, 1);
    v_keyName_661_ = crate::leanh::lean_ctor_get(v_pkg_659_, 2);
    crate::leanh::lean_inc(v_name_660_);
    crate::leanh::lean_inc(v_keyName_661_);
    v___x_662_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_662_, 0, v_keyName_661_);
    crate::leanh::lean_ctor_set(v___x_662_, 1, v_name_660_);
    return v___x_662_;
}
pub unsafe fn l_Lake_ConfigTarget_key___boxed(
    mut v_kind_663_: *mut crate::leanh::LeanObject,
    mut v_self_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Lake_ConfigTarget_key(v_kind_663_, v_self_664_);
    crate::leanh::lean_dec_ref(v_self_664_);
    crate::leanh::lean_dec(v_kind_663_);
    return v_res_665_;
}
pub unsafe fn l_Lake_LeanExe_exeBuildKey(
    mut v_self_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_667_ = crate::leanh::lean_ctor_get(v_self_666_, 0);
    v_name_668_ = crate::leanh::lean_ctor_get(v_self_666_, 1);
    v_keyName_669_ = crate::leanh::lean_ctor_get(v_pkg_667_, 2);
    crate::leanh::lean_inc(v_name_668_);
    crate::leanh::lean_inc(v_keyName_669_);
    v___x_670_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_670_, 0, v_keyName_669_);
    crate::leanh::lean_ctor_set(v___x_670_, 1, v_name_668_);
    v___x_671_ = l_Lake_LeanExe_exeFacet;
    v___x_672_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_672_, 0, v___x_670_);
    crate::leanh::lean_ctor_set(v___x_672_, 1, v___x_671_);
    return v___x_672_;
}
pub unsafe fn l_Lake_LeanExe_exeBuildKey___boxed(
    mut v_self_673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Lake_LeanExe_exeBuildKey(v_self_673_);
    crate::leanh::lean_dec_ref(v_self_673_);
    return v_res_674_;
}
pub unsafe fn l_Lake_ExternLib_staticBuildKey(
    mut v_self_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_676_ = crate::leanh::lean_ctor_get(v_self_675_, 0);
    v_name_677_ = crate::leanh::lean_ctor_get(v_self_675_, 1);
    v_keyName_678_ = crate::leanh::lean_ctor_get(v_pkg_676_, 2);
    crate::leanh::lean_inc(v_name_677_);
    crate::leanh::lean_inc(v_keyName_678_);
    v___x_679_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_679_, 0, v_keyName_678_);
    crate::leanh::lean_ctor_set(v___x_679_, 1, v_name_677_);
    v___x_680_ = l_Lake_ExternLib_staticFacet;
    v___x_681_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_681_, 0, v___x_679_);
    crate::leanh::lean_ctor_set(v___x_681_, 1, v___x_680_);
    return v___x_681_;
}
pub unsafe fn l_Lake_ExternLib_staticBuildKey___boxed(
    mut v_self_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Lake_ExternLib_staticBuildKey(v_self_682_);
    crate::leanh::lean_dec_ref(v_self_682_);
    return v_res_683_;
}
pub unsafe fn l_Lake_ExternLib_sharedBuildKey(
    mut v_self_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_685_ = crate::leanh::lean_ctor_get(v_self_684_, 0);
    v_name_686_ = crate::leanh::lean_ctor_get(v_self_684_, 1);
    v_keyName_687_ = crate::leanh::lean_ctor_get(v_pkg_685_, 2);
    crate::leanh::lean_inc(v_name_686_);
    crate::leanh::lean_inc(v_keyName_687_);
    v___x_688_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_688_, 0, v_keyName_687_);
    crate::leanh::lean_ctor_set(v___x_688_, 1, v_name_686_);
    v___x_689_ = l_Lake_ExternLib_sharedFacet;
    v___x_690_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_690_, 0, v___x_688_);
    crate::leanh::lean_ctor_set(v___x_690_, 1, v___x_689_);
    return v___x_690_;
}
pub unsafe fn l_Lake_ExternLib_sharedBuildKey___boxed(
    mut v_self_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Lake_ExternLib_sharedBuildKey(v_self_691_);
    crate::leanh::lean_dec_ref(v_self_691_);
    return v_res_692_;
}
pub unsafe fn l_Lake_ExternLib_dynlibBuildKey(
    mut v_self_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_694_ = crate::leanh::lean_ctor_get(v_self_693_, 0);
    v_name_695_ = crate::leanh::lean_ctor_get(v_self_693_, 1);
    v_keyName_696_ = crate::leanh::lean_ctor_get(v_pkg_694_, 2);
    crate::leanh::lean_inc(v_name_695_);
    crate::leanh::lean_inc(v_keyName_696_);
    v___x_697_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_697_, 0, v_keyName_696_);
    crate::leanh::lean_ctor_set(v___x_697_, 1, v_name_695_);
    v___x_698_ = l_Lake_ExternLib_dynlibFacet;
    v___x_699_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_699_, 0, v___x_697_);
    crate::leanh::lean_ctor_set(v___x_699_, 1, v___x_698_);
    return v___x_699_;
}
pub unsafe fn l_Lake_ExternLib_dynlibBuildKey___boxed(
    mut v_self_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lake_ExternLib_dynlibBuildKey(v_self_700_);
    crate::leanh::lean_dec_ref(v_self_700_);
    return v_res_701_;
}
pub unsafe fn l_Lake_Module_facetCore(
    mut v_facet_770_: *mut crate::leanh::LeanObject,
    mut v_self_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_772_ = crate::leanh::lean_ctor_get(v_self_771_, 0);
    v_pkg_773_ = crate::leanh::lean_ctor_get(v_lib_772_, 0);
    v_name_774_ = crate::leanh::lean_ctor_get(v_self_771_, 1);
    v_keyName_775_ = crate::leanh::lean_ctor_get(v_pkg_773_, 2);
    crate::leanh::lean_inc(v_name_774_);
    crate::leanh::lean_inc(v_keyName_775_);
    v___x_776_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_776_, 0, v_keyName_775_);
    crate::leanh::lean_ctor_set(v___x_776_, 1, v_name_774_);
    v___x_777_ = l_Lake_Module_keyword;
    v___x_778_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_776_);
    crate::leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
    crate::leanh::lean_ctor_set(v___x_778_, 2, v_self_771_);
    crate::leanh::lean_ctor_set(v___x_778_, 3, v_facet_770_);
    return v___x_778_;
}
pub unsafe fn l_Lake_Module_facet(
    mut v_facet_779_: *mut crate::leanh::LeanObject,
    mut v_self_780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_781_ = crate::leanh::lean_ctor_get(v_self_780_, 0);
    v_pkg_782_ = crate::leanh::lean_ctor_get(v_lib_781_, 0);
    v_name_783_ = crate::leanh::lean_ctor_get(v_self_780_, 1);
    v_keyName_784_ = crate::leanh::lean_ctor_get(v_pkg_782_, 2);
    v___x_785_ = l_Lake_Module_keyword;
    v___x_786_ = l_Lean_Name_append(v___x_785_, v_facet_779_);
    crate::leanh::lean_inc(v_name_783_);
    crate::leanh::lean_inc(v_keyName_784_);
    v___x_787_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_787_, 0, v_keyName_784_);
    crate::leanh::lean_ctor_set(v___x_787_, 1, v_name_783_);
    v___x_788_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_787_);
    crate::leanh::lean_ctor_set(v___x_788_, 1, v___x_785_);
    crate::leanh::lean_ctor_set(v___x_788_, 2, v_self_780_);
    crate::leanh::lean_ctor_set(v___x_788_, 3, v___x_786_);
    return v___x_788_;
}
pub unsafe fn l_Lake_Module_input(
    mut v_self_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_790_ = crate::leanh::lean_ctor_get(v_self_789_, 0);
    v_pkg_791_ = crate::leanh::lean_ctor_get(v_lib_790_, 0);
    v_name_792_ = crate::leanh::lean_ctor_get(v_self_789_, 1);
    v_keyName_793_ = crate::leanh::lean_ctor_get(v_pkg_791_, 2);
    v___x_794_ = l_Lake_Module_inputFacet;
    crate::leanh::lean_inc(v_name_792_);
    crate::leanh::lean_inc(v_keyName_793_);
    v___x_795_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_795_, 0, v_keyName_793_);
    crate::leanh::lean_ctor_set(v___x_795_, 1, v_name_792_);
    v___x_796_ = l_Lake_Module_keyword;
    v___x_797_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_795_);
    crate::leanh::lean_ctor_set(v___x_797_, 1, v___x_796_);
    crate::leanh::lean_ctor_set(v___x_797_, 2, v_self_789_);
    crate::leanh::lean_ctor_set(v___x_797_, 3, v___x_794_);
    return v___x_797_;
}
pub unsafe fn l_Lake_Module_lean(
    mut v_self_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_799_ = crate::leanh::lean_ctor_get(v_self_798_, 0);
    v_pkg_800_ = crate::leanh::lean_ctor_get(v_lib_799_, 0);
    v_name_801_ = crate::leanh::lean_ctor_get(v_self_798_, 1);
    v_keyName_802_ = crate::leanh::lean_ctor_get(v_pkg_800_, 2);
    v___x_803_ = l_Lake_Module_leanFacet;
    crate::leanh::lean_inc(v_name_801_);
    crate::leanh::lean_inc(v_keyName_802_);
    v___x_804_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_804_, 0, v_keyName_802_);
    crate::leanh::lean_ctor_set(v___x_804_, 1, v_name_801_);
    v___x_805_ = l_Lake_Module_keyword;
    v___x_806_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_806_, 0, v___x_804_);
    crate::leanh::lean_ctor_set(v___x_806_, 1, v___x_805_);
    crate::leanh::lean_ctor_set(v___x_806_, 2, v_self_798_);
    crate::leanh::lean_ctor_set(v___x_806_, 3, v___x_803_);
    return v___x_806_;
}
pub unsafe fn l_Lake_Module_header(
    mut v_self_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_808_ = crate::leanh::lean_ctor_get(v_self_807_, 0);
    v_pkg_809_ = crate::leanh::lean_ctor_get(v_lib_808_, 0);
    v_name_810_ = crate::leanh::lean_ctor_get(v_self_807_, 1);
    v_keyName_811_ = crate::leanh::lean_ctor_get(v_pkg_809_, 2);
    v___x_812_ = l_Lake_Module_headerFacet;
    crate::leanh::lean_inc(v_name_810_);
    crate::leanh::lean_inc(v_keyName_811_);
    v___x_813_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_813_, 0, v_keyName_811_);
    crate::leanh::lean_ctor_set(v___x_813_, 1, v_name_810_);
    v___x_814_ = l_Lake_Module_keyword;
    v___x_815_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_815_, 0, v___x_813_);
    crate::leanh::lean_ctor_set(v___x_815_, 1, v___x_814_);
    crate::leanh::lean_ctor_set(v___x_815_, 2, v_self_807_);
    crate::leanh::lean_ctor_set(v___x_815_, 3, v___x_812_);
    return v___x_815_;
}
pub unsafe fn l_Lake_Module_imports(
    mut v_self_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_817_ = crate::leanh::lean_ctor_get(v_self_816_, 0);
    v_pkg_818_ = crate::leanh::lean_ctor_get(v_lib_817_, 0);
    v_name_819_ = crate::leanh::lean_ctor_get(v_self_816_, 1);
    v_keyName_820_ = crate::leanh::lean_ctor_get(v_pkg_818_, 2);
    v___x_821_ = l_Lake_Module_importsFacet;
    crate::leanh::lean_inc(v_name_819_);
    crate::leanh::lean_inc(v_keyName_820_);
    v___x_822_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_822_, 0, v_keyName_820_);
    crate::leanh::lean_ctor_set(v___x_822_, 1, v_name_819_);
    v___x_823_ = l_Lake_Module_keyword;
    v___x_824_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_824_, 0, v___x_822_);
    crate::leanh::lean_ctor_set(v___x_824_, 1, v___x_823_);
    crate::leanh::lean_ctor_set(v___x_824_, 2, v_self_816_);
    crate::leanh::lean_ctor_set(v___x_824_, 3, v___x_821_);
    return v___x_824_;
}
pub unsafe fn l_Lake_Module_transImports(
    mut v_self_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_826_ = crate::leanh::lean_ctor_get(v_self_825_, 0);
    v_pkg_827_ = crate::leanh::lean_ctor_get(v_lib_826_, 0);
    v_name_828_ = crate::leanh::lean_ctor_get(v_self_825_, 1);
    v_keyName_829_ = crate::leanh::lean_ctor_get(v_pkg_827_, 2);
    v___x_830_ = l_Lake_Module_transImportsFacet;
    crate::leanh::lean_inc(v_name_828_);
    crate::leanh::lean_inc(v_keyName_829_);
    v___x_831_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_831_, 0, v_keyName_829_);
    crate::leanh::lean_ctor_set(v___x_831_, 1, v_name_828_);
    v___x_832_ = l_Lake_Module_keyword;
    v___x_833_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_833_, 0, v___x_831_);
    crate::leanh::lean_ctor_set(v___x_833_, 1, v___x_832_);
    crate::leanh::lean_ctor_set(v___x_833_, 2, v_self_825_);
    crate::leanh::lean_ctor_set(v___x_833_, 3, v___x_830_);
    return v___x_833_;
}
pub unsafe fn l_Lake_Module_precompileImports(
    mut v_self_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_835_ = crate::leanh::lean_ctor_get(v_self_834_, 0);
    v_pkg_836_ = crate::leanh::lean_ctor_get(v_lib_835_, 0);
    v_name_837_ = crate::leanh::lean_ctor_get(v_self_834_, 1);
    v_keyName_838_ = crate::leanh::lean_ctor_get(v_pkg_836_, 2);
    v___x_839_ = l_Lake_Module_precompileImportsFacet;
    crate::leanh::lean_inc(v_name_837_);
    crate::leanh::lean_inc(v_keyName_838_);
    v___x_840_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_840_, 0, v_keyName_838_);
    crate::leanh::lean_ctor_set(v___x_840_, 1, v_name_837_);
    v___x_841_ = l_Lake_Module_keyword;
    v___x_842_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_842_, 0, v___x_840_);
    crate::leanh::lean_ctor_set(v___x_842_, 1, v___x_841_);
    crate::leanh::lean_ctor_set(v___x_842_, 2, v_self_834_);
    crate::leanh::lean_ctor_set(v___x_842_, 3, v___x_839_);
    return v___x_842_;
}
pub unsafe fn l_Lake_Module_setup(
    mut v_self_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_844_ = crate::leanh::lean_ctor_get(v_self_843_, 0);
    v_pkg_845_ = crate::leanh::lean_ctor_get(v_lib_844_, 0);
    v_name_846_ = crate::leanh::lean_ctor_get(v_self_843_, 1);
    v_keyName_847_ = crate::leanh::lean_ctor_get(v_pkg_845_, 2);
    v___x_848_ = l_Lake_Module_setupFacet;
    crate::leanh::lean_inc(v_name_846_);
    crate::leanh::lean_inc(v_keyName_847_);
    v___x_849_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_849_, 0, v_keyName_847_);
    crate::leanh::lean_ctor_set(v___x_849_, 1, v_name_846_);
    v___x_850_ = l_Lake_Module_keyword;
    v___x_851_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_851_, 0, v___x_849_);
    crate::leanh::lean_ctor_set(v___x_851_, 1, v___x_850_);
    crate::leanh::lean_ctor_set(v___x_851_, 2, v_self_843_);
    crate::leanh::lean_ctor_set(v___x_851_, 3, v___x_848_);
    return v___x_851_;
}
pub unsafe fn l_Lake_Module_deps(
    mut v_self_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_853_ = crate::leanh::lean_ctor_get(v_self_852_, 0);
    v_pkg_854_ = crate::leanh::lean_ctor_get(v_lib_853_, 0);
    v_name_855_ = crate::leanh::lean_ctor_get(v_self_852_, 1);
    v_keyName_856_ = crate::leanh::lean_ctor_get(v_pkg_854_, 2);
    v___x_857_ = l_Lake_Module_depsFacet;
    crate::leanh::lean_inc(v_name_855_);
    crate::leanh::lean_inc(v_keyName_856_);
    v___x_858_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_858_, 0, v_keyName_856_);
    crate::leanh::lean_ctor_set(v___x_858_, 1, v_name_855_);
    v___x_859_ = l_Lake_Module_keyword;
    v___x_860_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_860_, 0, v___x_858_);
    crate::leanh::lean_ctor_set(v___x_860_, 1, v___x_859_);
    crate::leanh::lean_ctor_set(v___x_860_, 2, v_self_852_);
    crate::leanh::lean_ctor_set(v___x_860_, 3, v___x_857_);
    return v___x_860_;
}
pub unsafe fn l_Lake_Module_importInfo(
    mut v_self_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_862_ = crate::leanh::lean_ctor_get(v_self_861_, 0);
    v_pkg_863_ = crate::leanh::lean_ctor_get(v_lib_862_, 0);
    v_name_864_ = crate::leanh::lean_ctor_get(v_self_861_, 1);
    v_keyName_865_ = crate::leanh::lean_ctor_get(v_pkg_863_, 2);
    v___x_866_ = l_Lake_Module_importInfoFacet;
    crate::leanh::lean_inc(v_name_864_);
    crate::leanh::lean_inc(v_keyName_865_);
    v___x_867_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_867_, 0, v_keyName_865_);
    crate::leanh::lean_ctor_set(v___x_867_, 1, v_name_864_);
    v___x_868_ = l_Lake_Module_keyword;
    v___x_869_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_867_);
    crate::leanh::lean_ctor_set(v___x_869_, 1, v___x_868_);
    crate::leanh::lean_ctor_set(v___x_869_, 2, v_self_861_);
    crate::leanh::lean_ctor_set(v___x_869_, 3, v___x_866_);
    return v___x_869_;
}
pub unsafe fn l_Lake_Module_exportInfo(
    mut v_self_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_871_ = crate::leanh::lean_ctor_get(v_self_870_, 0);
    v_pkg_872_ = crate::leanh::lean_ctor_get(v_lib_871_, 0);
    v_name_873_ = crate::leanh::lean_ctor_get(v_self_870_, 1);
    v_keyName_874_ = crate::leanh::lean_ctor_get(v_pkg_872_, 2);
    v___x_875_ = l_Lake_Module_exportInfoFacet;
    crate::leanh::lean_inc(v_name_873_);
    crate::leanh::lean_inc(v_keyName_874_);
    v___x_876_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_876_, 0, v_keyName_874_);
    crate::leanh::lean_ctor_set(v___x_876_, 1, v_name_873_);
    v___x_877_ = l_Lake_Module_keyword;
    v___x_878_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_878_, 0, v___x_876_);
    crate::leanh::lean_ctor_set(v___x_878_, 1, v___x_877_);
    crate::leanh::lean_ctor_set(v___x_878_, 2, v_self_870_);
    crate::leanh::lean_ctor_set(v___x_878_, 3, v___x_875_);
    return v___x_878_;
}
pub unsafe fn l_Lake_Module_importArts(
    mut v_self_879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_880_ = crate::leanh::lean_ctor_get(v_self_879_, 0);
    v_pkg_881_ = crate::leanh::lean_ctor_get(v_lib_880_, 0);
    v_name_882_ = crate::leanh::lean_ctor_get(v_self_879_, 1);
    v_keyName_883_ = crate::leanh::lean_ctor_get(v_pkg_881_, 2);
    v___x_884_ = l_Lake_Module_importArtsFacet;
    crate::leanh::lean_inc(v_name_882_);
    crate::leanh::lean_inc(v_keyName_883_);
    v___x_885_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_885_, 0, v_keyName_883_);
    crate::leanh::lean_ctor_set(v___x_885_, 1, v_name_882_);
    v___x_886_ = l_Lake_Module_keyword;
    v___x_887_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_887_, 0, v___x_885_);
    crate::leanh::lean_ctor_set(v___x_887_, 1, v___x_886_);
    crate::leanh::lean_ctor_set(v___x_887_, 2, v_self_879_);
    crate::leanh::lean_ctor_set(v___x_887_, 3, v___x_884_);
    return v___x_887_;
}
pub unsafe fn l_Lake_Module_importAllArts(
    mut v_self_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_889_ = crate::leanh::lean_ctor_get(v_self_888_, 0);
    v_pkg_890_ = crate::leanh::lean_ctor_get(v_lib_889_, 0);
    v_name_891_ = crate::leanh::lean_ctor_get(v_self_888_, 1);
    v_keyName_892_ = crate::leanh::lean_ctor_get(v_pkg_890_, 2);
    v___x_893_ = l_Lake_Module_importAllArtsFacet;
    crate::leanh::lean_inc(v_name_891_);
    crate::leanh::lean_inc(v_keyName_892_);
    v___x_894_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_894_, 0, v_keyName_892_);
    crate::leanh::lean_ctor_set(v___x_894_, 1, v_name_891_);
    v___x_895_ = l_Lake_Module_keyword;
    v___x_896_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_894_);
    crate::leanh::lean_ctor_set(v___x_896_, 1, v___x_895_);
    crate::leanh::lean_ctor_set(v___x_896_, 2, v_self_888_);
    crate::leanh::lean_ctor_set(v___x_896_, 3, v___x_893_);
    return v___x_896_;
}
pub unsafe fn l_Lake_Module_leanArts(
    mut v_self_897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_898_ = crate::leanh::lean_ctor_get(v_self_897_, 0);
    v_pkg_899_ = crate::leanh::lean_ctor_get(v_lib_898_, 0);
    v_name_900_ = crate::leanh::lean_ctor_get(v_self_897_, 1);
    v_keyName_901_ = crate::leanh::lean_ctor_get(v_pkg_899_, 2);
    v___x_902_ = l_Lake_Module_leanArtsFacet;
    crate::leanh::lean_inc(v_name_900_);
    crate::leanh::lean_inc(v_keyName_901_);
    v___x_903_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_903_, 0, v_keyName_901_);
    crate::leanh::lean_ctor_set(v___x_903_, 1, v_name_900_);
    v___x_904_ = l_Lake_Module_keyword;
    v___x_905_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_905_, 0, v___x_903_);
    crate::leanh::lean_ctor_set(v___x_905_, 1, v___x_904_);
    crate::leanh::lean_ctor_set(v___x_905_, 2, v_self_897_);
    crate::leanh::lean_ctor_set(v___x_905_, 3, v___x_902_);
    return v___x_905_;
}
pub unsafe fn l_Lake_Module_olean(
    mut v_self_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_907_ = crate::leanh::lean_ctor_get(v_self_906_, 0);
    v_pkg_908_ = crate::leanh::lean_ctor_get(v_lib_907_, 0);
    v_name_909_ = crate::leanh::lean_ctor_get(v_self_906_, 1);
    v_keyName_910_ = crate::leanh::lean_ctor_get(v_pkg_908_, 2);
    v___x_911_ = l_Lake_Module_oleanFacet;
    crate::leanh::lean_inc(v_name_909_);
    crate::leanh::lean_inc(v_keyName_910_);
    v___x_912_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_912_, 0, v_keyName_910_);
    crate::leanh::lean_ctor_set(v___x_912_, 1, v_name_909_);
    v___x_913_ = l_Lake_Module_keyword;
    v___x_914_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_914_, 0, v___x_912_);
    crate::leanh::lean_ctor_set(v___x_914_, 1, v___x_913_);
    crate::leanh::lean_ctor_set(v___x_914_, 2, v_self_906_);
    crate::leanh::lean_ctor_set(v___x_914_, 3, v___x_911_);
    return v___x_914_;
}
pub unsafe fn l_Lake_Module_oleanServer(
    mut v_self_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_916_ = crate::leanh::lean_ctor_get(v_self_915_, 0);
    v_pkg_917_ = crate::leanh::lean_ctor_get(v_lib_916_, 0);
    v_name_918_ = crate::leanh::lean_ctor_get(v_self_915_, 1);
    v_keyName_919_ = crate::leanh::lean_ctor_get(v_pkg_917_, 2);
    v___x_920_ = l_Lake_Module_oleanServerFacet;
    crate::leanh::lean_inc(v_name_918_);
    crate::leanh::lean_inc(v_keyName_919_);
    v___x_921_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_921_, 0, v_keyName_919_);
    crate::leanh::lean_ctor_set(v___x_921_, 1, v_name_918_);
    v___x_922_ = l_Lake_Module_keyword;
    v___x_923_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_921_);
    crate::leanh::lean_ctor_set(v___x_923_, 1, v___x_922_);
    crate::leanh::lean_ctor_set(v___x_923_, 2, v_self_915_);
    crate::leanh::lean_ctor_set(v___x_923_, 3, v___x_920_);
    return v___x_923_;
}
pub unsafe fn l_Lake_Module_oleanPrivate(
    mut v_self_924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_925_ = crate::leanh::lean_ctor_get(v_self_924_, 0);
    v_pkg_926_ = crate::leanh::lean_ctor_get(v_lib_925_, 0);
    v_name_927_ = crate::leanh::lean_ctor_get(v_self_924_, 1);
    v_keyName_928_ = crate::leanh::lean_ctor_get(v_pkg_926_, 2);
    v___x_929_ = l_Lake_Module_oleanPrivateFacet;
    crate::leanh::lean_inc(v_name_927_);
    crate::leanh::lean_inc(v_keyName_928_);
    v___x_930_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_930_, 0, v_keyName_928_);
    crate::leanh::lean_ctor_set(v___x_930_, 1, v_name_927_);
    v___x_931_ = l_Lake_Module_keyword;
    v___x_932_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_932_, 0, v___x_930_);
    crate::leanh::lean_ctor_set(v___x_932_, 1, v___x_931_);
    crate::leanh::lean_ctor_set(v___x_932_, 2, v_self_924_);
    crate::leanh::lean_ctor_set(v___x_932_, 3, v___x_929_);
    return v___x_932_;
}
pub unsafe fn l_Lake_Module_ilean(
    mut v_self_933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_934_ = crate::leanh::lean_ctor_get(v_self_933_, 0);
    v_pkg_935_ = crate::leanh::lean_ctor_get(v_lib_934_, 0);
    v_name_936_ = crate::leanh::lean_ctor_get(v_self_933_, 1);
    v_keyName_937_ = crate::leanh::lean_ctor_get(v_pkg_935_, 2);
    v___x_938_ = l_Lake_Module_ileanFacet;
    crate::leanh::lean_inc(v_name_936_);
    crate::leanh::lean_inc(v_keyName_937_);
    v___x_939_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_939_, 0, v_keyName_937_);
    crate::leanh::lean_ctor_set(v___x_939_, 1, v_name_936_);
    v___x_940_ = l_Lake_Module_keyword;
    v___x_941_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_941_, 0, v___x_939_);
    crate::leanh::lean_ctor_set(v___x_941_, 1, v___x_940_);
    crate::leanh::lean_ctor_set(v___x_941_, 2, v_self_933_);
    crate::leanh::lean_ctor_set(v___x_941_, 3, v___x_938_);
    return v___x_941_;
}
pub unsafe fn l_Lake_Module_ir(
    mut v_self_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_943_ = crate::leanh::lean_ctor_get(v_self_942_, 0);
    v_pkg_944_ = crate::leanh::lean_ctor_get(v_lib_943_, 0);
    v_name_945_ = crate::leanh::lean_ctor_get(v_self_942_, 1);
    v_keyName_946_ = crate::leanh::lean_ctor_get(v_pkg_944_, 2);
    v___x_947_ = l_Lake_Module_irFacet;
    crate::leanh::lean_inc(v_name_945_);
    crate::leanh::lean_inc(v_keyName_946_);
    v___x_948_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_948_, 0, v_keyName_946_);
    crate::leanh::lean_ctor_set(v___x_948_, 1, v_name_945_);
    v___x_949_ = l_Lake_Module_keyword;
    v___x_950_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_948_);
    crate::leanh::lean_ctor_set(v___x_950_, 1, v___x_949_);
    crate::leanh::lean_ctor_set(v___x_950_, 2, v_self_942_);
    crate::leanh::lean_ctor_set(v___x_950_, 3, v___x_947_);
    return v___x_950_;
}
pub unsafe fn l_Lake_Module_c(
    mut v_self_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_952_ = crate::leanh::lean_ctor_get(v_self_951_, 0);
    v_pkg_953_ = crate::leanh::lean_ctor_get(v_lib_952_, 0);
    v_name_954_ = crate::leanh::lean_ctor_get(v_self_951_, 1);
    v_keyName_955_ = crate::leanh::lean_ctor_get(v_pkg_953_, 2);
    v___x_956_ = l_Lake_Module_cFacet;
    crate::leanh::lean_inc(v_name_954_);
    crate::leanh::lean_inc(v_keyName_955_);
    v___x_957_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_957_, 0, v_keyName_955_);
    crate::leanh::lean_ctor_set(v___x_957_, 1, v_name_954_);
    v___x_958_ = l_Lake_Module_keyword;
    v___x_959_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_959_, 0, v___x_957_);
    crate::leanh::lean_ctor_set(v___x_959_, 1, v___x_958_);
    crate::leanh::lean_ctor_set(v___x_959_, 2, v_self_951_);
    crate::leanh::lean_ctor_set(v___x_959_, 3, v___x_956_);
    return v___x_959_;
}
pub unsafe fn l_Lake_Module_bc(
    mut v_self_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_961_ = crate::leanh::lean_ctor_get(v_self_960_, 0);
    v_pkg_962_ = crate::leanh::lean_ctor_get(v_lib_961_, 0);
    v_name_963_ = crate::leanh::lean_ctor_get(v_self_960_, 1);
    v_keyName_964_ = crate::leanh::lean_ctor_get(v_pkg_962_, 2);
    v___x_965_ = l_Lake_Module_bcFacet;
    crate::leanh::lean_inc(v_name_963_);
    crate::leanh::lean_inc(v_keyName_964_);
    v___x_966_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_966_, 0, v_keyName_964_);
    crate::leanh::lean_ctor_set(v___x_966_, 1, v_name_963_);
    v___x_967_ = l_Lake_Module_keyword;
    v___x_968_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_968_, 0, v___x_966_);
    crate::leanh::lean_ctor_set(v___x_968_, 1, v___x_967_);
    crate::leanh::lean_ctor_set(v___x_968_, 2, v_self_960_);
    crate::leanh::lean_ctor_set(v___x_968_, 3, v___x_965_);
    return v___x_968_;
}
pub unsafe fn l_Lake_Module_ltar(
    mut v_self_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_970_ = crate::leanh::lean_ctor_get(v_self_969_, 0);
    v_pkg_971_ = crate::leanh::lean_ctor_get(v_lib_970_, 0);
    v_name_972_ = crate::leanh::lean_ctor_get(v_self_969_, 1);
    v_keyName_973_ = crate::leanh::lean_ctor_get(v_pkg_971_, 2);
    v___x_974_ = l_Lake_Module_ltarFacet;
    crate::leanh::lean_inc(v_name_972_);
    crate::leanh::lean_inc(v_keyName_973_);
    v___x_975_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_975_, 0, v_keyName_973_);
    crate::leanh::lean_ctor_set(v___x_975_, 1, v_name_972_);
    v___x_976_ = l_Lake_Module_keyword;
    v___x_977_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_975_);
    crate::leanh::lean_ctor_set(v___x_977_, 1, v___x_976_);
    crate::leanh::lean_ctor_set(v___x_977_, 2, v_self_969_);
    crate::leanh::lean_ctor_set(v___x_977_, 3, v___x_974_);
    return v___x_977_;
}
pub unsafe fn l_Lake_Module_o(
    mut v_self_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_979_ = crate::leanh::lean_ctor_get(v_self_978_, 0);
    v_pkg_980_ = crate::leanh::lean_ctor_get(v_lib_979_, 0);
    v_name_981_ = crate::leanh::lean_ctor_get(v_self_978_, 1);
    v_keyName_982_ = crate::leanh::lean_ctor_get(v_pkg_980_, 2);
    v___x_983_ = l_Lake_Module_oFacet;
    crate::leanh::lean_inc(v_name_981_);
    crate::leanh::lean_inc(v_keyName_982_);
    v___x_984_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_984_, 0, v_keyName_982_);
    crate::leanh::lean_ctor_set(v___x_984_, 1, v_name_981_);
    v___x_985_ = l_Lake_Module_keyword;
    v___x_986_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_986_, 0, v___x_984_);
    crate::leanh::lean_ctor_set(v___x_986_, 1, v___x_985_);
    crate::leanh::lean_ctor_set(v___x_986_, 2, v_self_978_);
    crate::leanh::lean_ctor_set(v___x_986_, 3, v___x_983_);
    return v___x_986_;
}
pub unsafe fn l_Lake_Module_oExport(
    mut v_self_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_988_ = crate::leanh::lean_ctor_get(v_self_987_, 0);
    v_pkg_989_ = crate::leanh::lean_ctor_get(v_lib_988_, 0);
    v_name_990_ = crate::leanh::lean_ctor_get(v_self_987_, 1);
    v_keyName_991_ = crate::leanh::lean_ctor_get(v_pkg_989_, 2);
    v___x_992_ = l_Lake_Module_oExportFacet;
    crate::leanh::lean_inc(v_name_990_);
    crate::leanh::lean_inc(v_keyName_991_);
    v___x_993_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_993_, 0, v_keyName_991_);
    crate::leanh::lean_ctor_set(v___x_993_, 1, v_name_990_);
    v___x_994_ = l_Lake_Module_keyword;
    v___x_995_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_995_, 0, v___x_993_);
    crate::leanh::lean_ctor_set(v___x_995_, 1, v___x_994_);
    crate::leanh::lean_ctor_set(v___x_995_, 2, v_self_987_);
    crate::leanh::lean_ctor_set(v___x_995_, 3, v___x_992_);
    return v___x_995_;
}
pub unsafe fn l_Lake_Module_oNoExport(
    mut v_self_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_997_ = crate::leanh::lean_ctor_get(v_self_996_, 0);
    v_pkg_998_ = crate::leanh::lean_ctor_get(v_lib_997_, 0);
    v_name_999_ = crate::leanh::lean_ctor_get(v_self_996_, 1);
    v_keyName_1000_ = crate::leanh::lean_ctor_get(v_pkg_998_, 2);
    v___x_1001_ = l_Lake_Module_oNoExportFacet;
    crate::leanh::lean_inc(v_name_999_);
    crate::leanh::lean_inc(v_keyName_1000_);
    v___x_1002_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1002_, 0, v_keyName_1000_);
    crate::leanh::lean_ctor_set(v___x_1002_, 1, v_name_999_);
    v___x_1003_ = l_Lake_Module_keyword;
    v___x_1004_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_1002_);
    crate::leanh::lean_ctor_set(v___x_1004_, 1, v___x_1003_);
    crate::leanh::lean_ctor_set(v___x_1004_, 2, v_self_996_);
    crate::leanh::lean_ctor_set(v___x_1004_, 3, v___x_1001_);
    return v___x_1004_;
}
pub unsafe fn l_Lake_Module_co(
    mut v_self_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1006_ = crate::leanh::lean_ctor_get(v_self_1005_, 0);
    v_pkg_1007_ = crate::leanh::lean_ctor_get(v_lib_1006_, 0);
    v_name_1008_ = crate::leanh::lean_ctor_get(v_self_1005_, 1);
    v_keyName_1009_ = crate::leanh::lean_ctor_get(v_pkg_1007_, 2);
    v___x_1010_ = l_Lake_Module_coFacet;
    crate::leanh::lean_inc(v_name_1008_);
    crate::leanh::lean_inc(v_keyName_1009_);
    v___x_1011_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1011_, 0, v_keyName_1009_);
    crate::leanh::lean_ctor_set(v___x_1011_, 1, v_name_1008_);
    v___x_1012_ = l_Lake_Module_keyword;
    v___x_1013_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_1011_);
    crate::leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
    crate::leanh::lean_ctor_set(v___x_1013_, 2, v_self_1005_);
    crate::leanh::lean_ctor_set(v___x_1013_, 3, v___x_1010_);
    return v___x_1013_;
}
pub unsafe fn l_Lake_Module_coExport(
    mut v_self_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1015_ = crate::leanh::lean_ctor_get(v_self_1014_, 0);
    v_pkg_1016_ = crate::leanh::lean_ctor_get(v_lib_1015_, 0);
    v_name_1017_ = crate::leanh::lean_ctor_get(v_self_1014_, 1);
    v_keyName_1018_ = crate::leanh::lean_ctor_get(v_pkg_1016_, 2);
    v___x_1019_ = l_Lake_Module_coExportFacet;
    crate::leanh::lean_inc(v_name_1017_);
    crate::leanh::lean_inc(v_keyName_1018_);
    v___x_1020_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1020_, 0, v_keyName_1018_);
    crate::leanh::lean_ctor_set(v___x_1020_, 1, v_name_1017_);
    v___x_1021_ = l_Lake_Module_keyword;
    v___x_1022_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1022_, 0, v___x_1020_);
    crate::leanh::lean_ctor_set(v___x_1022_, 1, v___x_1021_);
    crate::leanh::lean_ctor_set(v___x_1022_, 2, v_self_1014_);
    crate::leanh::lean_ctor_set(v___x_1022_, 3, v___x_1019_);
    return v___x_1022_;
}
pub unsafe fn l_Lake_Module_coNoExport(
    mut v_self_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1024_ = crate::leanh::lean_ctor_get(v_self_1023_, 0);
    v_pkg_1025_ = crate::leanh::lean_ctor_get(v_lib_1024_, 0);
    v_name_1026_ = crate::leanh::lean_ctor_get(v_self_1023_, 1);
    v_keyName_1027_ = crate::leanh::lean_ctor_get(v_pkg_1025_, 2);
    v___x_1028_ = l_Lake_Module_coNoExportFacet;
    crate::leanh::lean_inc(v_name_1026_);
    crate::leanh::lean_inc(v_keyName_1027_);
    v___x_1029_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1029_, 0, v_keyName_1027_);
    crate::leanh::lean_ctor_set(v___x_1029_, 1, v_name_1026_);
    v___x_1030_ = l_Lake_Module_keyword;
    v___x_1031_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1031_, 0, v___x_1029_);
    crate::leanh::lean_ctor_set(v___x_1031_, 1, v___x_1030_);
    crate::leanh::lean_ctor_set(v___x_1031_, 2, v_self_1023_);
    crate::leanh::lean_ctor_set(v___x_1031_, 3, v___x_1028_);
    return v___x_1031_;
}
pub unsafe fn l_Lake_Module_bco(
    mut v_self_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1033_ = crate::leanh::lean_ctor_get(v_self_1032_, 0);
    v_pkg_1034_ = crate::leanh::lean_ctor_get(v_lib_1033_, 0);
    v_name_1035_ = crate::leanh::lean_ctor_get(v_self_1032_, 1);
    v_keyName_1036_ = crate::leanh::lean_ctor_get(v_pkg_1034_, 2);
    v___x_1037_ = l_Lake_Module_bcoFacet;
    crate::leanh::lean_inc(v_name_1035_);
    crate::leanh::lean_inc(v_keyName_1036_);
    v___x_1038_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1038_, 0, v_keyName_1036_);
    crate::leanh::lean_ctor_set(v___x_1038_, 1, v_name_1035_);
    v___x_1039_ = l_Lake_Module_keyword;
    v___x_1040_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1040_, 0, v___x_1038_);
    crate::leanh::lean_ctor_set(v___x_1040_, 1, v___x_1039_);
    crate::leanh::lean_ctor_set(v___x_1040_, 2, v_self_1032_);
    crate::leanh::lean_ctor_set(v___x_1040_, 3, v___x_1037_);
    return v___x_1040_;
}
pub unsafe fn l_Lake_Module_dynlib(
    mut v_self_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1042_ = crate::leanh::lean_ctor_get(v_self_1041_, 0);
    v_pkg_1043_ = crate::leanh::lean_ctor_get(v_lib_1042_, 0);
    v_name_1044_ = crate::leanh::lean_ctor_get(v_self_1041_, 1);
    v_keyName_1045_ = crate::leanh::lean_ctor_get(v_pkg_1043_, 2);
    v___x_1046_ = l_Lake_Module_dynlibFacet;
    crate::leanh::lean_inc(v_name_1044_);
    crate::leanh::lean_inc(v_keyName_1045_);
    v___x_1047_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1047_, 0, v_keyName_1045_);
    crate::leanh::lean_ctor_set(v___x_1047_, 1, v_name_1044_);
    v___x_1048_ = l_Lake_Module_keyword;
    v___x_1049_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1049_, 0, v___x_1047_);
    crate::leanh::lean_ctor_set(v___x_1049_, 1, v___x_1048_);
    crate::leanh::lean_ctor_set(v___x_1049_, 2, v_self_1041_);
    crate::leanh::lean_ctor_set(v___x_1049_, 3, v___x_1046_);
    return v___x_1049_;
}
pub unsafe fn l_Lake_Package_target(
    mut v_target_1050_: *mut crate::leanh::LeanObject,
    mut v_self_1051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1052_, 0, v_self_1051_);
    crate::leanh::lean_ctor_set(v___x_1052_, 1, v_target_1050_);
    return v___x_1052_;
}
pub unsafe fn l_Lake_Package_facetCore(
    mut v_facet_1053_: *mut crate::leanh::LeanObject,
    mut v_self_1054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1055_ = crate::leanh::lean_ctor_get(v_self_1054_, 2);
    crate::leanh::lean_inc(v_keyName_1055_);
    v___x_1056_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1056_, 0, v_keyName_1055_);
    v___x_1057_ = l_Lake_Package_keyword;
    v___x_1058_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1058_, 0, v___x_1056_);
    crate::leanh::lean_ctor_set(v___x_1058_, 1, v___x_1057_);
    crate::leanh::lean_ctor_set(v___x_1058_, 2, v_self_1054_);
    crate::leanh::lean_ctor_set(v___x_1058_, 3, v_facet_1053_);
    return v___x_1058_;
}
pub unsafe fn l_Lake_Package_facet(
    mut v_facet_1059_: *mut crate::leanh::LeanObject,
    mut v_self_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1061_ = crate::leanh::lean_ctor_get(v_self_1060_, 2);
    v___x_1062_ = l_Lake_Package_keyword;
    v___x_1063_ = l_Lean_Name_append(v___x_1062_, v_facet_1059_);
    crate::leanh::lean_inc(v_keyName_1061_);
    v___x_1064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1064_, 0, v_keyName_1061_);
    v___x_1065_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1065_, 0, v___x_1064_);
    crate::leanh::lean_ctor_set(v___x_1065_, 1, v___x_1062_);
    crate::leanh::lean_ctor_set(v___x_1065_, 2, v_self_1060_);
    crate::leanh::lean_ctor_set(v___x_1065_, 3, v___x_1063_);
    return v___x_1065_;
}
pub unsafe fn l_Lake_Package_buildCache(
    mut v_self_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1067_ = crate::leanh::lean_ctor_get(v_self_1066_, 2);
    v___x_1068_ = l_Lake_Package_buildCacheFacet;
    crate::leanh::lean_inc(v_keyName_1067_);
    v___x_1069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1069_, 0, v_keyName_1067_);
    v___x_1070_ = l_Lake_Package_keyword;
    v___x_1071_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1071_, 0, v___x_1069_);
    crate::leanh::lean_ctor_set(v___x_1071_, 1, v___x_1070_);
    crate::leanh::lean_ctor_set(v___x_1071_, 2, v_self_1066_);
    crate::leanh::lean_ctor_set(v___x_1071_, 3, v___x_1068_);
    return v___x_1071_;
}
pub unsafe fn l_Lake_Package_optBuildCache(
    mut v_self_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1073_ = crate::leanh::lean_ctor_get(v_self_1072_, 2);
    v___x_1074_ = l_Lake_Package_optBuildCacheFacet;
    crate::leanh::lean_inc(v_keyName_1073_);
    v___x_1075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1075_, 0, v_keyName_1073_);
    v___x_1076_ = l_Lake_Package_keyword;
    v___x_1077_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1077_, 0, v___x_1075_);
    crate::leanh::lean_ctor_set(v___x_1077_, 1, v___x_1076_);
    crate::leanh::lean_ctor_set(v___x_1077_, 2, v_self_1072_);
    crate::leanh::lean_ctor_set(v___x_1077_, 3, v___x_1074_);
    return v___x_1077_;
}
pub unsafe fn l_Lake_Package_reservoirBarrel(
    mut v_self_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1079_ = crate::leanh::lean_ctor_get(v_self_1078_, 2);
    v___x_1080_ = l_Lake_Package_reservoirBarrelFacet;
    crate::leanh::lean_inc(v_keyName_1079_);
    v___x_1081_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1081_, 0, v_keyName_1079_);
    v___x_1082_ = l_Lake_Package_keyword;
    v___x_1083_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1083_, 0, v___x_1081_);
    crate::leanh::lean_ctor_set(v___x_1083_, 1, v___x_1082_);
    crate::leanh::lean_ctor_set(v___x_1083_, 2, v_self_1078_);
    crate::leanh::lean_ctor_set(v___x_1083_, 3, v___x_1080_);
    return v___x_1083_;
}
pub unsafe fn l_Lake_Package_optReservoirBarrel(
    mut v_self_1084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1085_ = crate::leanh::lean_ctor_get(v_self_1084_, 2);
    v___x_1086_ = l_Lake_Package_optReservoirBarrelFacet;
    crate::leanh::lean_inc(v_keyName_1085_);
    v___x_1087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1087_, 0, v_keyName_1085_);
    v___x_1088_ = l_Lake_Package_keyword;
    v___x_1089_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1089_, 0, v___x_1087_);
    crate::leanh::lean_ctor_set(v___x_1089_, 1, v___x_1088_);
    crate::leanh::lean_ctor_set(v___x_1089_, 2, v_self_1084_);
    crate::leanh::lean_ctor_set(v___x_1089_, 3, v___x_1086_);
    return v___x_1089_;
}
pub unsafe fn l_Lake_Package_gitHubRelease(
    mut v_self_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1091_ = crate::leanh::lean_ctor_get(v_self_1090_, 2);
    v___x_1092_ = l_Lake_Package_gitHubReleaseFacet;
    crate::leanh::lean_inc(v_keyName_1091_);
    v___x_1093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1093_, 0, v_keyName_1091_);
    v___x_1094_ = l_Lake_Package_keyword;
    v___x_1095_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1095_, 0, v___x_1093_);
    crate::leanh::lean_ctor_set(v___x_1095_, 1, v___x_1094_);
    crate::leanh::lean_ctor_set(v___x_1095_, 2, v_self_1090_);
    crate::leanh::lean_ctor_set(v___x_1095_, 3, v___x_1092_);
    return v___x_1095_;
}
pub unsafe fn l_Lake_Package_optGitHubRelease(
    mut v_self_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1097_ = crate::leanh::lean_ctor_get(v_self_1096_, 2);
    v___x_1098_ = l_Lake_Package_optGitHubReleaseFacet;
    crate::leanh::lean_inc(v_keyName_1097_);
    v___x_1099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1099_, 0, v_keyName_1097_);
    v___x_1100_ = l_Lake_Package_keyword;
    v___x_1101_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1101_, 0, v___x_1099_);
    crate::leanh::lean_ctor_set(v___x_1101_, 1, v___x_1100_);
    crate::leanh::lean_ctor_set(v___x_1101_, 2, v_self_1096_);
    crate::leanh::lean_ctor_set(v___x_1101_, 3, v___x_1098_);
    return v___x_1101_;
}
pub unsafe fn l_Lake_Package_extraDep(
    mut v_self_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1103_ = crate::leanh::lean_ctor_get(v_self_1102_, 2);
    v___x_1104_ = l_Lake_Package_extraDepFacet;
    crate::leanh::lean_inc(v_keyName_1103_);
    v___x_1105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1105_, 0, v_keyName_1103_);
    v___x_1106_ = l_Lake_Package_keyword;
    v___x_1107_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1107_, 0, v___x_1105_);
    crate::leanh::lean_ctor_set(v___x_1107_, 1, v___x_1106_);
    crate::leanh::lean_ctor_set(v___x_1107_, 2, v_self_1102_);
    crate::leanh::lean_ctor_set(v___x_1107_, 3, v___x_1104_);
    return v___x_1107_;
}
pub unsafe fn l_Lake_Package_deps(
    mut v_self_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1109_ = crate::leanh::lean_ctor_get(v_self_1108_, 2);
    v___x_1110_ = l_Lake_Package_depsFacet;
    crate::leanh::lean_inc(v_keyName_1109_);
    v___x_1111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1111_, 0, v_keyName_1109_);
    v___x_1112_ = l_Lake_Package_keyword;
    v___x_1113_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1113_, 0, v___x_1111_);
    crate::leanh::lean_ctor_set(v___x_1113_, 1, v___x_1112_);
    crate::leanh::lean_ctor_set(v___x_1113_, 2, v_self_1108_);
    crate::leanh::lean_ctor_set(v___x_1113_, 3, v___x_1110_);
    return v___x_1113_;
}
pub unsafe fn l_Lake_Package_transDeps(
    mut v_self_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1115_ = crate::leanh::lean_ctor_get(v_self_1114_, 2);
    v___x_1116_ = l_Lake_Package_transDepsFacet;
    crate::leanh::lean_inc(v_keyName_1115_);
    v___x_1117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1117_, 0, v_keyName_1115_);
    v___x_1118_ = l_Lake_Package_keyword;
    v___x_1119_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1119_, 0, v___x_1117_);
    crate::leanh::lean_ctor_set(v___x_1119_, 1, v___x_1118_);
    crate::leanh::lean_ctor_set(v___x_1119_, 2, v_self_1114_);
    crate::leanh::lean_ctor_set(v___x_1119_, 3, v___x_1116_);
    return v___x_1119_;
}
pub unsafe fn l_Lake_LeanLib_facetCore(
    mut v_facet_1120_: *mut crate::leanh::LeanObject,
    mut v_self_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1122_ = crate::leanh::lean_ctor_get(v_self_1121_, 0);
    v_name_1123_ = crate::leanh::lean_ctor_get(v_self_1121_, 1);
    v_keyName_1124_ = crate::leanh::lean_ctor_get(v_pkg_1122_, 2);
    crate::leanh::lean_inc(v_name_1123_);
    crate::leanh::lean_inc(v_keyName_1124_);
    v___x_1125_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1125_, 0, v_keyName_1124_);
    crate::leanh::lean_ctor_set(v___x_1125_, 1, v_name_1123_);
    v___x_1126_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1127_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1127_, 0, v___x_1125_);
    crate::leanh::lean_ctor_set(v___x_1127_, 1, v___x_1126_);
    crate::leanh::lean_ctor_set(v___x_1127_, 2, v_self_1121_);
    crate::leanh::lean_ctor_set(v___x_1127_, 3, v_facet_1120_);
    return v___x_1127_;
}
pub unsafe fn l_Lake_LeanLib_facet(
    mut v_facet_1128_: *mut crate::leanh::LeanObject,
    mut v_self_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1130_ = crate::leanh::lean_ctor_get(v_self_1129_, 0);
    v_name_1131_ = crate::leanh::lean_ctor_get(v_self_1129_, 1);
    v_keyName_1132_ = crate::leanh::lean_ctor_get(v_pkg_1130_, 2);
    v___x_1133_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1134_ = l_Lean_Name_append(v___x_1133_, v_facet_1128_);
    crate::leanh::lean_inc(v_name_1131_);
    crate::leanh::lean_inc(v_keyName_1132_);
    v___x_1135_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1135_, 0, v_keyName_1132_);
    crate::leanh::lean_ctor_set(v___x_1135_, 1, v_name_1131_);
    v___x_1136_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1136_, 0, v___x_1135_);
    crate::leanh::lean_ctor_set(v___x_1136_, 1, v___x_1133_);
    crate::leanh::lean_ctor_set(v___x_1136_, 2, v_self_1129_);
    crate::leanh::lean_ctor_set(v___x_1136_, 3, v___x_1134_);
    return v___x_1136_;
}
pub unsafe fn l_Lake_LeanLib_default(
    mut v_self_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1138_ = crate::leanh::lean_ctor_get(v_self_1137_, 0);
    v_name_1139_ = crate::leanh::lean_ctor_get(v_self_1137_, 1);
    v_keyName_1140_ = crate::leanh::lean_ctor_get(v_pkg_1138_, 2);
    v___x_1141_ = l_Lake_LeanLib_defaultFacet;
    crate::leanh::lean_inc(v_name_1139_);
    crate::leanh::lean_inc(v_keyName_1140_);
    v___x_1142_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1142_, 0, v_keyName_1140_);
    crate::leanh::lean_ctor_set(v___x_1142_, 1, v_name_1139_);
    v___x_1143_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1144_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1144_, 0, v___x_1142_);
    crate::leanh::lean_ctor_set(v___x_1144_, 1, v___x_1143_);
    crate::leanh::lean_ctor_set(v___x_1144_, 2, v_self_1137_);
    crate::leanh::lean_ctor_set(v___x_1144_, 3, v___x_1141_);
    return v___x_1144_;
}
pub unsafe fn l_Lake_LeanLib_modules(
    mut v_self_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1146_ = crate::leanh::lean_ctor_get(v_self_1145_, 0);
    v_name_1147_ = crate::leanh::lean_ctor_get(v_self_1145_, 1);
    v_keyName_1148_ = crate::leanh::lean_ctor_get(v_pkg_1146_, 2);
    v___x_1149_ = l_Lake_LeanLib_modulesFacet;
    crate::leanh::lean_inc(v_name_1147_);
    crate::leanh::lean_inc(v_keyName_1148_);
    v___x_1150_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1150_, 0, v_keyName_1148_);
    crate::leanh::lean_ctor_set(v___x_1150_, 1, v_name_1147_);
    v___x_1151_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1152_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1152_, 0, v___x_1150_);
    crate::leanh::lean_ctor_set(v___x_1152_, 1, v___x_1151_);
    crate::leanh::lean_ctor_set(v___x_1152_, 2, v_self_1145_);
    crate::leanh::lean_ctor_set(v___x_1152_, 3, v___x_1149_);
    return v___x_1152_;
}
pub unsafe fn l_Lake_LeanLib_leanArts(
    mut v_self_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1154_ = crate::leanh::lean_ctor_get(v_self_1153_, 0);
    v_name_1155_ = crate::leanh::lean_ctor_get(v_self_1153_, 1);
    v_keyName_1156_ = crate::leanh::lean_ctor_get(v_pkg_1154_, 2);
    v___x_1157_ = l_Lake_LeanLib_leanArtsFacet;
    crate::leanh::lean_inc(v_name_1155_);
    crate::leanh::lean_inc(v_keyName_1156_);
    v___x_1158_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1158_, 0, v_keyName_1156_);
    crate::leanh::lean_ctor_set(v___x_1158_, 1, v_name_1155_);
    v___x_1159_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1160_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1160_, 0, v___x_1158_);
    crate::leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    crate::leanh::lean_ctor_set(v___x_1160_, 2, v_self_1153_);
    crate::leanh::lean_ctor_set(v___x_1160_, 3, v___x_1157_);
    return v___x_1160_;
}
pub unsafe fn l_Lake_LeanLib_static(
    mut v_self_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1162_ = crate::leanh::lean_ctor_get(v_self_1161_, 0);
    v_name_1163_ = crate::leanh::lean_ctor_get(v_self_1161_, 1);
    v_keyName_1164_ = crate::leanh::lean_ctor_get(v_pkg_1162_, 2);
    v___x_1165_ = l_Lake_LeanLib_staticFacet;
    crate::leanh::lean_inc(v_name_1163_);
    crate::leanh::lean_inc(v_keyName_1164_);
    v___x_1166_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1166_, 0, v_keyName_1164_);
    crate::leanh::lean_ctor_set(v___x_1166_, 1, v_name_1163_);
    v___x_1167_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1168_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1168_, 0, v___x_1166_);
    crate::leanh::lean_ctor_set(v___x_1168_, 1, v___x_1167_);
    crate::leanh::lean_ctor_set(v___x_1168_, 2, v_self_1161_);
    crate::leanh::lean_ctor_set(v___x_1168_, 3, v___x_1165_);
    return v___x_1168_;
}
pub unsafe fn l_Lake_LeanLib_staticExport(
    mut v_self_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1170_ = crate::leanh::lean_ctor_get(v_self_1169_, 0);
    v_name_1171_ = crate::leanh::lean_ctor_get(v_self_1169_, 1);
    v_keyName_1172_ = crate::leanh::lean_ctor_get(v_pkg_1170_, 2);
    v___x_1173_ = l_Lake_LeanLib_staticExportFacet;
    crate::leanh::lean_inc(v_name_1171_);
    crate::leanh::lean_inc(v_keyName_1172_);
    v___x_1174_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1174_, 0, v_keyName_1172_);
    crate::leanh::lean_ctor_set(v___x_1174_, 1, v_name_1171_);
    v___x_1175_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1176_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1176_, 0, v___x_1174_);
    crate::leanh::lean_ctor_set(v___x_1176_, 1, v___x_1175_);
    crate::leanh::lean_ctor_set(v___x_1176_, 2, v_self_1169_);
    crate::leanh::lean_ctor_set(v___x_1176_, 3, v___x_1173_);
    return v___x_1176_;
}
pub unsafe fn l_Lake_LeanLib_shared(
    mut v_self_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1178_ = crate::leanh::lean_ctor_get(v_self_1177_, 0);
    v_name_1179_ = crate::leanh::lean_ctor_get(v_self_1177_, 1);
    v_keyName_1180_ = crate::leanh::lean_ctor_get(v_pkg_1178_, 2);
    v___x_1181_ = l_Lake_LeanLib_sharedFacet;
    crate::leanh::lean_inc(v_name_1179_);
    crate::leanh::lean_inc(v_keyName_1180_);
    v___x_1182_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1182_, 0, v_keyName_1180_);
    crate::leanh::lean_ctor_set(v___x_1182_, 1, v_name_1179_);
    v___x_1183_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1184_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1184_, 0, v___x_1182_);
    crate::leanh::lean_ctor_set(v___x_1184_, 1, v___x_1183_);
    crate::leanh::lean_ctor_set(v___x_1184_, 2, v_self_1177_);
    crate::leanh::lean_ctor_set(v___x_1184_, 3, v___x_1181_);
    return v___x_1184_;
}
pub unsafe fn l_Lake_LeanLib_extraDep(
    mut v_self_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1186_ = crate::leanh::lean_ctor_get(v_self_1185_, 0);
    v_name_1187_ = crate::leanh::lean_ctor_get(v_self_1185_, 1);
    v_keyName_1188_ = crate::leanh::lean_ctor_get(v_pkg_1186_, 2);
    v___x_1189_ = l_Lake_LeanLib_extraDepFacet;
    crate::leanh::lean_inc(v_name_1187_);
    crate::leanh::lean_inc(v_keyName_1188_);
    v___x_1190_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1190_, 0, v_keyName_1188_);
    crate::leanh::lean_ctor_set(v___x_1190_, 1, v_name_1187_);
    v___x_1191_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1192_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1192_, 0, v___x_1190_);
    crate::leanh::lean_ctor_set(v___x_1192_, 1, v___x_1191_);
    crate::leanh::lean_ctor_set(v___x_1192_, 2, v_self_1185_);
    crate::leanh::lean_ctor_set(v___x_1192_, 3, v___x_1189_);
    return v___x_1192_;
}
pub unsafe fn l_Lake_LeanExe_facetCore(
    mut v_facet_1193_: *mut crate::leanh::LeanObject,
    mut v_self_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1195_ = crate::leanh::lean_ctor_get(v_self_1194_, 0);
    v_name_1196_ = crate::leanh::lean_ctor_get(v_self_1194_, 1);
    v_keyName_1197_ = crate::leanh::lean_ctor_get(v_pkg_1195_, 2);
    crate::leanh::lean_inc(v_name_1196_);
    crate::leanh::lean_inc(v_keyName_1197_);
    v___x_1198_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1198_, 0, v_keyName_1197_);
    crate::leanh::lean_ctor_set(v___x_1198_, 1, v_name_1196_);
    v___x_1199_ = l_Lake_LeanExe_keyword;
    v___x_1200_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1200_, 0, v___x_1198_);
    crate::leanh::lean_ctor_set(v___x_1200_, 1, v___x_1199_);
    crate::leanh::lean_ctor_set(v___x_1200_, 2, v_self_1194_);
    crate::leanh::lean_ctor_set(v___x_1200_, 3, v_facet_1193_);
    return v___x_1200_;
}
pub unsafe fn l_Lake_LeanExe_exe(
    mut v_self_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1202_ = crate::leanh::lean_ctor_get(v_self_1201_, 0);
    v_name_1203_ = crate::leanh::lean_ctor_get(v_self_1201_, 1);
    v_keyName_1204_ = crate::leanh::lean_ctor_get(v_pkg_1202_, 2);
    v___x_1205_ = l_Lake_LeanExe_exeFacet;
    crate::leanh::lean_inc(v_name_1203_);
    crate::leanh::lean_inc(v_keyName_1204_);
    v___x_1206_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1206_, 0, v_keyName_1204_);
    crate::leanh::lean_ctor_set(v___x_1206_, 1, v_name_1203_);
    v___x_1207_ = l_Lake_LeanExe_keyword;
    v___x_1208_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1208_, 0, v___x_1206_);
    crate::leanh::lean_ctor_set(v___x_1208_, 1, v___x_1207_);
    crate::leanh::lean_ctor_set(v___x_1208_, 2, v_self_1201_);
    crate::leanh::lean_ctor_set(v___x_1208_, 3, v___x_1205_);
    return v___x_1208_;
}
pub unsafe fn l_Lake_ExternLib_facetCore(
    mut v_facet_1209_: *mut crate::leanh::LeanObject,
    mut v_self_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1211_ = crate::leanh::lean_ctor_get(v_self_1210_, 0);
    v_name_1212_ = crate::leanh::lean_ctor_get(v_self_1210_, 1);
    v_keyName_1213_ = crate::leanh::lean_ctor_get(v_pkg_1211_, 2);
    crate::leanh::lean_inc(v_name_1212_);
    crate::leanh::lean_inc(v_keyName_1213_);
    v___x_1214_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1214_, 0, v_keyName_1213_);
    crate::leanh::lean_ctor_set(v___x_1214_, 1, v_name_1212_);
    v___x_1215_ = l_Lake_ExternLib_keyword;
    v___x_1216_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1216_, 0, v___x_1214_);
    crate::leanh::lean_ctor_set(v___x_1216_, 1, v___x_1215_);
    crate::leanh::lean_ctor_set(v___x_1216_, 2, v_self_1210_);
    crate::leanh::lean_ctor_set(v___x_1216_, 3, v_facet_1209_);
    return v___x_1216_;
}
pub unsafe fn l_Lake_ExternLib_static(
    mut v_self_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1218_ = crate::leanh::lean_ctor_get(v_self_1217_, 0);
    v_name_1219_ = crate::leanh::lean_ctor_get(v_self_1217_, 1);
    v_keyName_1220_ = crate::leanh::lean_ctor_get(v_pkg_1218_, 2);
    v___x_1221_ = l_Lake_ExternLib_staticFacet;
    crate::leanh::lean_inc(v_name_1219_);
    crate::leanh::lean_inc(v_keyName_1220_);
    v___x_1222_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1222_, 0, v_keyName_1220_);
    crate::leanh::lean_ctor_set(v___x_1222_, 1, v_name_1219_);
    v___x_1223_ = l_Lake_ExternLib_keyword;
    v___x_1224_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1224_, 0, v___x_1222_);
    crate::leanh::lean_ctor_set(v___x_1224_, 1, v___x_1223_);
    crate::leanh::lean_ctor_set(v___x_1224_, 2, v_self_1217_);
    crate::leanh::lean_ctor_set(v___x_1224_, 3, v___x_1221_);
    return v___x_1224_;
}
pub unsafe fn l_Lake_ExternLib_shared(
    mut v_self_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1226_ = crate::leanh::lean_ctor_get(v_self_1225_, 0);
    v_name_1227_ = crate::leanh::lean_ctor_get(v_self_1225_, 1);
    v_keyName_1228_ = crate::leanh::lean_ctor_get(v_pkg_1226_, 2);
    v___x_1229_ = l_Lake_ExternLib_sharedFacet;
    crate::leanh::lean_inc(v_name_1227_);
    crate::leanh::lean_inc(v_keyName_1228_);
    v___x_1230_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1230_, 0, v_keyName_1228_);
    crate::leanh::lean_ctor_set(v___x_1230_, 1, v_name_1227_);
    v___x_1231_ = l_Lake_ExternLib_keyword;
    v___x_1232_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1232_, 0, v___x_1230_);
    crate::leanh::lean_ctor_set(v___x_1232_, 1, v___x_1231_);
    crate::leanh::lean_ctor_set(v___x_1232_, 2, v_self_1225_);
    crate::leanh::lean_ctor_set(v___x_1232_, 3, v___x_1229_);
    return v___x_1232_;
}
pub unsafe fn l_Lake_ExternLib_dynlib(
    mut v_self_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1234_ = crate::leanh::lean_ctor_get(v_self_1233_, 0);
    v_name_1235_ = crate::leanh::lean_ctor_get(v_self_1233_, 1);
    v_keyName_1236_ = crate::leanh::lean_ctor_get(v_pkg_1234_, 2);
    v___x_1237_ = l_Lake_ExternLib_dynlibFacet;
    crate::leanh::lean_inc(v_name_1235_);
    crate::leanh::lean_inc(v_keyName_1236_);
    v___x_1238_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1238_, 0, v_keyName_1236_);
    crate::leanh::lean_ctor_set(v___x_1238_, 1, v_name_1235_);
    v___x_1239_ = l_Lake_ExternLib_keyword;
    v___x_1240_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1240_, 0, v___x_1238_);
    crate::leanh::lean_ctor_set(v___x_1240_, 1, v___x_1239_);
    crate::leanh::lean_ctor_set(v___x_1240_, 2, v_self_1233_);
    crate::leanh::lean_ctor_set(v___x_1240_, 3, v___x_1237_);
    return v___x_1240_;
}
pub unsafe fn l_Lake_InputFile_facetCore(
    mut v_facet_1241_: *mut crate::leanh::LeanObject,
    mut v_self_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1243_ = crate::leanh::lean_ctor_get(v_self_1242_, 0);
    v_name_1244_ = crate::leanh::lean_ctor_get(v_self_1242_, 1);
    v_keyName_1245_ = crate::leanh::lean_ctor_get(v_pkg_1243_, 2);
    crate::leanh::lean_inc(v_name_1244_);
    crate::leanh::lean_inc(v_keyName_1245_);
    v___x_1246_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1246_, 0, v_keyName_1245_);
    crate::leanh::lean_ctor_set(v___x_1246_, 1, v_name_1244_);
    v___x_1247_ = l_Lake_InputFile_keyword;
    v___x_1248_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1248_, 0, v___x_1246_);
    crate::leanh::lean_ctor_set(v___x_1248_, 1, v___x_1247_);
    crate::leanh::lean_ctor_set(v___x_1248_, 2, v_self_1242_);
    crate::leanh::lean_ctor_set(v___x_1248_, 3, v_facet_1241_);
    return v___x_1248_;
}
pub unsafe fn l_Lake_InputFile_default(
    mut v_self_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1250_ = crate::leanh::lean_ctor_get(v_self_1249_, 0);
    v_name_1251_ = crate::leanh::lean_ctor_get(v_self_1249_, 1);
    v_keyName_1252_ = crate::leanh::lean_ctor_get(v_pkg_1250_, 2);
    v___x_1253_ = l_Lake_InputFile_defaultFacet;
    crate::leanh::lean_inc(v_name_1251_);
    crate::leanh::lean_inc(v_keyName_1252_);
    v___x_1254_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1254_, 0, v_keyName_1252_);
    crate::leanh::lean_ctor_set(v___x_1254_, 1, v_name_1251_);
    v___x_1255_ = l_Lake_InputFile_keyword;
    v___x_1256_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1256_, 0, v___x_1254_);
    crate::leanh::lean_ctor_set(v___x_1256_, 1, v___x_1255_);
    crate::leanh::lean_ctor_set(v___x_1256_, 2, v_self_1249_);
    crate::leanh::lean_ctor_set(v___x_1256_, 3, v___x_1253_);
    return v___x_1256_;
}
pub unsafe fn l_Lake_InputDir_facetCore(
    mut v_facet_1257_: *mut crate::leanh::LeanObject,
    mut v_self_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1259_ = crate::leanh::lean_ctor_get(v_self_1258_, 0);
    v_name_1260_ = crate::leanh::lean_ctor_get(v_self_1258_, 1);
    v_keyName_1261_ = crate::leanh::lean_ctor_get(v_pkg_1259_, 2);
    crate::leanh::lean_inc(v_name_1260_);
    crate::leanh::lean_inc(v_keyName_1261_);
    v___x_1262_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1262_, 0, v_keyName_1261_);
    crate::leanh::lean_ctor_set(v___x_1262_, 1, v_name_1260_);
    v___x_1263_ = l_Lake_InputDir_keyword;
    v___x_1264_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1262_);
    crate::leanh::lean_ctor_set(v___x_1264_, 1, v___x_1263_);
    crate::leanh::lean_ctor_set(v___x_1264_, 2, v_self_1258_);
    crate::leanh::lean_ctor_set(v___x_1264_, 3, v_facet_1257_);
    return v___x_1264_;
}
pub unsafe fn l_Lake_InputDir_default(
    mut v_self_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1266_ = crate::leanh::lean_ctor_get(v_self_1265_, 0);
    v_name_1267_ = crate::leanh::lean_ctor_get(v_self_1265_, 1);
    v_keyName_1268_ = crate::leanh::lean_ctor_get(v_pkg_1266_, 2);
    v___x_1269_ = l_Lake_InputDir_defaultFacet;
    crate::leanh::lean_inc(v_name_1267_);
    crate::leanh::lean_inc(v_keyName_1268_);
    v___x_1270_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1270_, 0, v_keyName_1268_);
    crate::leanh::lean_ctor_set(v___x_1270_, 1, v_name_1267_);
    v___x_1271_ = l_Lake_InputDir_keyword;
    v___x_1272_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1272_, 0, v___x_1270_);
    crate::leanh::lean_ctor_set(v___x_1272_, 1, v___x_1271_);
    crate::leanh::lean_ctor_set(v___x_1272_, 2, v_self_1265_);
    crate::leanh::lean_ctor_set(v___x_1272_, 3, v___x_1269_);
    return v___x_1272_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Infos(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Info(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Infos(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Build_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Infos(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Info(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LeanExe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_ExternLib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_InputFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Infos(builtin);
}
