// Lean compiler output
// Module: Lake.Build.Infos
// Imports: Lake.Build.Info Lake.Config.LeanExe Lake.Config.ExternLib Lake.Config.InputFile Lake.Build.Data
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
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
pub static l_Lake_instDataKindModule___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instDataKindModule___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindModule___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut leanh::LeanObject,
            5134674735115079031 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindModule___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instDataKindModule: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindPackage___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instDataKindPackage___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindPackage___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value)
                as *mut leanh::LeanObject,
            6671755061125946191 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindPackage___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instDataKindPackage: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindLeanLib___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instDataKindLeanLib___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindLeanLib___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value)
                as *mut leanh::LeanObject,
            12295998048739818339 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindLeanLib___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instDataKindLeanLib: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindLeanExe___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instDataKindLeanExe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindLeanExe___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__0_value)
                as *mut leanh::LeanObject,
            10587356296225942211 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindLeanExe___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instDataKindLeanExe: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindExternLib___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instDataKindExternLib___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindExternLib___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__0_value)
                as *mut leanh::LeanObject,
            11562366611225967008 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindExternLib___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instDataKindExternLib: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindInputFile___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instDataKindInputFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindInputFile___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__0_value)
                as *mut leanh::LeanObject,
            4067501922346325234 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindInputFile___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instDataKindInputFile: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindInputDir___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instDataKindInputDir___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instDataKindInputDir___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__0_value)
                as *mut leanh::LeanObject,
            9710019104504222840 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instDataKindInputDir___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instDataKindInputDir: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_inputFacet___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Module_inputFacet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Module_inputFacet___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut leanh::LeanObject,
            5134674735115079031 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_inputFacet___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__0_value)
                as *mut leanh::LeanObject,
            14553655559741226012 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_inputFacet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Module_inputFacet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_importsFacet___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Module_importsFacet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Module_importsFacet___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut leanh::LeanObject,
            5134674735115079031 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_importsFacet___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__0_value)
                as *mut leanh::LeanObject,
            6906776088522269727 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_importsFacet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Module_importsFacet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_transImportsFacet___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Module_transImportsFacet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Module_transImportsFacet___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut leanh::LeanObject,
            5134674735115079031 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_transImportsFacet___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__0_value)
                as *mut leanh::LeanObject,
            15145167986846249592 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_transImportsFacet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Module_transImportsFacet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_precompileImportsFacet___closed__0_value: leanh::LeanStringObject<
    18,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_Module_precompileImportsFacet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Module_precompileImportsFacet___closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
            as *mut leanh::LeanObject,
        5134674735115079031 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_Module_precompileImportsFacet___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__0_value)
                as *mut leanh::LeanObject,
            9286526061556025856 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_precompileImportsFacet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Module_precompileImportsFacet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_dynlibFacet___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Module_dynlibFacet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Module_dynlibFacet___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value)
                as *mut leanh::LeanObject,
            5134674735115079031 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_dynlibFacet___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__0_value)
                as *mut leanh::LeanObject,
            18425581243965226140 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_dynlibFacet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Module_dynlibFacet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanLib_modulesFacet___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_LeanLib_modulesFacet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_LeanLib_modulesFacet___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value)
                as *mut leanh::LeanObject,
            12295998048739818339 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanLib_modulesFacet___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__0_value)
                as *mut leanh::LeanObject,
            15633005100005579590 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_modulesFacet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanLib_modulesFacet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_depsFacet___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Package_depsFacet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Package_depsFacet___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value)
                as *mut leanh::LeanObject,
            6671755061125946191 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Package_depsFacet___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__0_value)
                as *mut leanh::LeanObject,
            8196140624318363255 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_depsFacet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Package_depsFacet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Package_transDepsFacet___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Package_transDepsFacet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Package_transDepsFacet___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value)
                as *mut leanh::LeanObject,
            6671755061125946191 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Package_transDepsFacet___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__0_value)
                as *mut leanh::LeanObject,
            15594444263647844606 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_transDepsFacet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Package_transDepsFacet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_Module_key(
    mut v_self_637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_643_: u8 = 0;
    let mut v_keyName_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut v_unused_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_638_ = leanh::lean_ctor_get(v_self_637_, 0);
                v_pkg_639_ = leanh::lean_ctor_get(v_lib_638_, 0);
                leanh::lean_inc_ref(v_pkg_639_);
                v_name_640_ = leanh::lean_ctor_get(v_self_637_, 1);
                v_isSharedCheck_648_ = (!leanh::lean_is_exclusive(v_self_637_)) as u8;
                if v_isSharedCheck_648_ == 0 {
                    v_unused_649_ = leanh::lean_ctor_get(v_self_637_, 0);
                    leanh::lean_dec(v_unused_649_);
                    v___x_642_ = v_self_637_;
                    v_isShared_643_ = v_isSharedCheck_648_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_name_640_);
                    leanh::lean_dec(v_self_637_);
                    v___x_642_ = leanh::lean_box(0);
                    v_isShared_643_ = v_isSharedCheck_648_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_keyName_644_ = leanh::lean_ctor_get(v_pkg_639_, 2);
                leanh::lean_inc(v_keyName_644_);
                leanh::lean_dec_ref(v_pkg_639_);
                if v_isShared_643_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_642_, 2);
                    leanh::lean_ctor_set(v___x_642_, 0, v_keyName_644_);
                    v___x_646_ = v___x_642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_647_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_647_, 0, v_keyName_644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_647_, 1, v_name_640_);
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
    mut v_self_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_651_ = leanh::lean_ctor_get(v_self_650_, 0);
    v_name_652_ = leanh::lean_ctor_get(v_self_650_, 1);
    v_keyName_653_ = leanh::lean_ctor_get(v_pkg_651_, 2);
    leanh::lean_inc(v_name_652_);
    leanh::lean_inc(v_keyName_653_);
    v___x_654_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_654_, 0, v_keyName_653_);
    leanh::lean_ctor_set(v___x_654_, 1, v_name_652_);
    return v___x_654_;
}
pub unsafe fn l_Lake_ConfigTarget_key___redArg___boxed(
    mut v_self_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_656_ = l_Lake_ConfigTarget_key___redArg(v_self_655_);
    leanh::lean_dec_ref(v_self_655_);
    return v_res_656_;
}
pub unsafe fn l_Lake_ConfigTarget_key(
    mut v_kind_657_: *mut leanh::LeanObject,
    mut v_self_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_659_ = leanh::lean_ctor_get(v_self_658_, 0);
    v_name_660_ = leanh::lean_ctor_get(v_self_658_, 1);
    v_keyName_661_ = leanh::lean_ctor_get(v_pkg_659_, 2);
    leanh::lean_inc(v_name_660_);
    leanh::lean_inc(v_keyName_661_);
    v___x_662_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_662_, 0, v_keyName_661_);
    leanh::lean_ctor_set(v___x_662_, 1, v_name_660_);
    return v___x_662_;
}
pub unsafe fn l_Lake_ConfigTarget_key___boxed(
    mut v_kind_663_: *mut leanh::LeanObject,
    mut v_self_664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Lake_ConfigTarget_key(v_kind_663_, v_self_664_);
    leanh::lean_dec_ref(v_self_664_);
    leanh::lean_dec(v_kind_663_);
    return v_res_665_;
}
pub unsafe fn l_Lake_LeanExe_exeBuildKey(
    mut v_self_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_667_ = leanh::lean_ctor_get(v_self_666_, 0);
    v_name_668_ = leanh::lean_ctor_get(v_self_666_, 1);
    v_keyName_669_ = leanh::lean_ctor_get(v_pkg_667_, 2);
    leanh::lean_inc(v_name_668_);
    leanh::lean_inc(v_keyName_669_);
    v___x_670_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_670_, 0, v_keyName_669_);
    leanh::lean_ctor_set(v___x_670_, 1, v_name_668_);
    v___x_671_ = l_Lake_LeanExe_exeFacet;
    v___x_672_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_672_, 0, v___x_670_);
    leanh::lean_ctor_set(v___x_672_, 1, v___x_671_);
    return v___x_672_;
}
pub unsafe fn l_Lake_LeanExe_exeBuildKey___boxed(
    mut v_self_673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Lake_LeanExe_exeBuildKey(v_self_673_);
    leanh::lean_dec_ref(v_self_673_);
    return v_res_674_;
}
pub unsafe fn l_Lake_ExternLib_staticBuildKey(
    mut v_self_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_676_ = leanh::lean_ctor_get(v_self_675_, 0);
    v_name_677_ = leanh::lean_ctor_get(v_self_675_, 1);
    v_keyName_678_ = leanh::lean_ctor_get(v_pkg_676_, 2);
    leanh::lean_inc(v_name_677_);
    leanh::lean_inc(v_keyName_678_);
    v___x_679_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_679_, 0, v_keyName_678_);
    leanh::lean_ctor_set(v___x_679_, 1, v_name_677_);
    v___x_680_ = l_Lake_ExternLib_staticFacet;
    v___x_681_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_681_, 0, v___x_679_);
    leanh::lean_ctor_set(v___x_681_, 1, v___x_680_);
    return v___x_681_;
}
pub unsafe fn l_Lake_ExternLib_staticBuildKey___boxed(
    mut v_self_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Lake_ExternLib_staticBuildKey(v_self_682_);
    leanh::lean_dec_ref(v_self_682_);
    return v_res_683_;
}
pub unsafe fn l_Lake_ExternLib_sharedBuildKey(
    mut v_self_684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_685_ = leanh::lean_ctor_get(v_self_684_, 0);
    v_name_686_ = leanh::lean_ctor_get(v_self_684_, 1);
    v_keyName_687_ = leanh::lean_ctor_get(v_pkg_685_, 2);
    leanh::lean_inc(v_name_686_);
    leanh::lean_inc(v_keyName_687_);
    v___x_688_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_688_, 0, v_keyName_687_);
    leanh::lean_ctor_set(v___x_688_, 1, v_name_686_);
    v___x_689_ = l_Lake_ExternLib_sharedFacet;
    v___x_690_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_690_, 0, v___x_688_);
    leanh::lean_ctor_set(v___x_690_, 1, v___x_689_);
    return v___x_690_;
}
pub unsafe fn l_Lake_ExternLib_sharedBuildKey___boxed(
    mut v_self_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Lake_ExternLib_sharedBuildKey(v_self_691_);
    leanh::lean_dec_ref(v_self_691_);
    return v_res_692_;
}
pub unsafe fn l_Lake_ExternLib_dynlibBuildKey(
    mut v_self_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_694_ = leanh::lean_ctor_get(v_self_693_, 0);
    v_name_695_ = leanh::lean_ctor_get(v_self_693_, 1);
    v_keyName_696_ = leanh::lean_ctor_get(v_pkg_694_, 2);
    leanh::lean_inc(v_name_695_);
    leanh::lean_inc(v_keyName_696_);
    v___x_697_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_697_, 0, v_keyName_696_);
    leanh::lean_ctor_set(v___x_697_, 1, v_name_695_);
    v___x_698_ = l_Lake_ExternLib_dynlibFacet;
    v___x_699_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_699_, 0, v___x_697_);
    leanh::lean_ctor_set(v___x_699_, 1, v___x_698_);
    return v___x_699_;
}
pub unsafe fn l_Lake_ExternLib_dynlibBuildKey___boxed(
    mut v_self_700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lake_ExternLib_dynlibBuildKey(v_self_700_);
    leanh::lean_dec_ref(v_self_700_);
    return v_res_701_;
}
pub unsafe fn l_Lake_Module_facetCore(
    mut v_facet_770_: *mut leanh::LeanObject,
    mut v_self_771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_772_ = leanh::lean_ctor_get(v_self_771_, 0);
    v_pkg_773_ = leanh::lean_ctor_get(v_lib_772_, 0);
    v_name_774_ = leanh::lean_ctor_get(v_self_771_, 1);
    v_keyName_775_ = leanh::lean_ctor_get(v_pkg_773_, 2);
    leanh::lean_inc(v_name_774_);
    leanh::lean_inc(v_keyName_775_);
    v___x_776_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_776_, 0, v_keyName_775_);
    leanh::lean_ctor_set(v___x_776_, 1, v_name_774_);
    v___x_777_ = l_Lake_Module_keyword;
    v___x_778_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_778_, 0, v___x_776_);
    leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
    leanh::lean_ctor_set(v___x_778_, 2, v_self_771_);
    leanh::lean_ctor_set(v___x_778_, 3, v_facet_770_);
    return v___x_778_;
}
pub unsafe fn l_Lake_Module_facet(
    mut v_facet_779_: *mut leanh::LeanObject,
    mut v_self_780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_781_ = leanh::lean_ctor_get(v_self_780_, 0);
    v_pkg_782_ = leanh::lean_ctor_get(v_lib_781_, 0);
    v_name_783_ = leanh::lean_ctor_get(v_self_780_, 1);
    v_keyName_784_ = leanh::lean_ctor_get(v_pkg_782_, 2);
    v___x_785_ = l_Lake_Module_keyword;
    v___x_786_ = l_Lean_Name_append(v___x_785_, v_facet_779_);
    leanh::lean_inc(v_name_783_);
    leanh::lean_inc(v_keyName_784_);
    v___x_787_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_787_, 0, v_keyName_784_);
    leanh::lean_ctor_set(v___x_787_, 1, v_name_783_);
    v___x_788_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_788_, 0, v___x_787_);
    leanh::lean_ctor_set(v___x_788_, 1, v___x_785_);
    leanh::lean_ctor_set(v___x_788_, 2, v_self_780_);
    leanh::lean_ctor_set(v___x_788_, 3, v___x_786_);
    return v___x_788_;
}
pub unsafe fn l_Lake_Module_input(
    mut v_self_789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_790_ = leanh::lean_ctor_get(v_self_789_, 0);
    v_pkg_791_ = leanh::lean_ctor_get(v_lib_790_, 0);
    v_name_792_ = leanh::lean_ctor_get(v_self_789_, 1);
    v_keyName_793_ = leanh::lean_ctor_get(v_pkg_791_, 2);
    v___x_794_ = l_Lake_Module_inputFacet;
    leanh::lean_inc(v_name_792_);
    leanh::lean_inc(v_keyName_793_);
    v___x_795_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_795_, 0, v_keyName_793_);
    leanh::lean_ctor_set(v___x_795_, 1, v_name_792_);
    v___x_796_ = l_Lake_Module_keyword;
    v___x_797_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_797_, 0, v___x_795_);
    leanh::lean_ctor_set(v___x_797_, 1, v___x_796_);
    leanh::lean_ctor_set(v___x_797_, 2, v_self_789_);
    leanh::lean_ctor_set(v___x_797_, 3, v___x_794_);
    return v___x_797_;
}
pub unsafe fn l_Lake_Module_lean(
    mut v_self_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_799_ = leanh::lean_ctor_get(v_self_798_, 0);
    v_pkg_800_ = leanh::lean_ctor_get(v_lib_799_, 0);
    v_name_801_ = leanh::lean_ctor_get(v_self_798_, 1);
    v_keyName_802_ = leanh::lean_ctor_get(v_pkg_800_, 2);
    v___x_803_ = l_Lake_Module_leanFacet;
    leanh::lean_inc(v_name_801_);
    leanh::lean_inc(v_keyName_802_);
    v___x_804_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_804_, 0, v_keyName_802_);
    leanh::lean_ctor_set(v___x_804_, 1, v_name_801_);
    v___x_805_ = l_Lake_Module_keyword;
    v___x_806_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_806_, 0, v___x_804_);
    leanh::lean_ctor_set(v___x_806_, 1, v___x_805_);
    leanh::lean_ctor_set(v___x_806_, 2, v_self_798_);
    leanh::lean_ctor_set(v___x_806_, 3, v___x_803_);
    return v___x_806_;
}
pub unsafe fn l_Lake_Module_header(
    mut v_self_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_808_ = leanh::lean_ctor_get(v_self_807_, 0);
    v_pkg_809_ = leanh::lean_ctor_get(v_lib_808_, 0);
    v_name_810_ = leanh::lean_ctor_get(v_self_807_, 1);
    v_keyName_811_ = leanh::lean_ctor_get(v_pkg_809_, 2);
    v___x_812_ = l_Lake_Module_headerFacet;
    leanh::lean_inc(v_name_810_);
    leanh::lean_inc(v_keyName_811_);
    v___x_813_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_813_, 0, v_keyName_811_);
    leanh::lean_ctor_set(v___x_813_, 1, v_name_810_);
    v___x_814_ = l_Lake_Module_keyword;
    v___x_815_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_815_, 0, v___x_813_);
    leanh::lean_ctor_set(v___x_815_, 1, v___x_814_);
    leanh::lean_ctor_set(v___x_815_, 2, v_self_807_);
    leanh::lean_ctor_set(v___x_815_, 3, v___x_812_);
    return v___x_815_;
}
pub unsafe fn l_Lake_Module_imports(
    mut v_self_816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_817_ = leanh::lean_ctor_get(v_self_816_, 0);
    v_pkg_818_ = leanh::lean_ctor_get(v_lib_817_, 0);
    v_name_819_ = leanh::lean_ctor_get(v_self_816_, 1);
    v_keyName_820_ = leanh::lean_ctor_get(v_pkg_818_, 2);
    v___x_821_ = l_Lake_Module_importsFacet;
    leanh::lean_inc(v_name_819_);
    leanh::lean_inc(v_keyName_820_);
    v___x_822_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_822_, 0, v_keyName_820_);
    leanh::lean_ctor_set(v___x_822_, 1, v_name_819_);
    v___x_823_ = l_Lake_Module_keyword;
    v___x_824_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_824_, 0, v___x_822_);
    leanh::lean_ctor_set(v___x_824_, 1, v___x_823_);
    leanh::lean_ctor_set(v___x_824_, 2, v_self_816_);
    leanh::lean_ctor_set(v___x_824_, 3, v___x_821_);
    return v___x_824_;
}
pub unsafe fn l_Lake_Module_transImports(
    mut v_self_825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_826_ = leanh::lean_ctor_get(v_self_825_, 0);
    v_pkg_827_ = leanh::lean_ctor_get(v_lib_826_, 0);
    v_name_828_ = leanh::lean_ctor_get(v_self_825_, 1);
    v_keyName_829_ = leanh::lean_ctor_get(v_pkg_827_, 2);
    v___x_830_ = l_Lake_Module_transImportsFacet;
    leanh::lean_inc(v_name_828_);
    leanh::lean_inc(v_keyName_829_);
    v___x_831_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_831_, 0, v_keyName_829_);
    leanh::lean_ctor_set(v___x_831_, 1, v_name_828_);
    v___x_832_ = l_Lake_Module_keyword;
    v___x_833_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_833_, 0, v___x_831_);
    leanh::lean_ctor_set(v___x_833_, 1, v___x_832_);
    leanh::lean_ctor_set(v___x_833_, 2, v_self_825_);
    leanh::lean_ctor_set(v___x_833_, 3, v___x_830_);
    return v___x_833_;
}
pub unsafe fn l_Lake_Module_precompileImports(
    mut v_self_834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_835_ = leanh::lean_ctor_get(v_self_834_, 0);
    v_pkg_836_ = leanh::lean_ctor_get(v_lib_835_, 0);
    v_name_837_ = leanh::lean_ctor_get(v_self_834_, 1);
    v_keyName_838_ = leanh::lean_ctor_get(v_pkg_836_, 2);
    v___x_839_ = l_Lake_Module_precompileImportsFacet;
    leanh::lean_inc(v_name_837_);
    leanh::lean_inc(v_keyName_838_);
    v___x_840_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_840_, 0, v_keyName_838_);
    leanh::lean_ctor_set(v___x_840_, 1, v_name_837_);
    v___x_841_ = l_Lake_Module_keyword;
    v___x_842_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_842_, 0, v___x_840_);
    leanh::lean_ctor_set(v___x_842_, 1, v___x_841_);
    leanh::lean_ctor_set(v___x_842_, 2, v_self_834_);
    leanh::lean_ctor_set(v___x_842_, 3, v___x_839_);
    return v___x_842_;
}
pub unsafe fn l_Lake_Module_setup(
    mut v_self_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_844_ = leanh::lean_ctor_get(v_self_843_, 0);
    v_pkg_845_ = leanh::lean_ctor_get(v_lib_844_, 0);
    v_name_846_ = leanh::lean_ctor_get(v_self_843_, 1);
    v_keyName_847_ = leanh::lean_ctor_get(v_pkg_845_, 2);
    v___x_848_ = l_Lake_Module_setupFacet;
    leanh::lean_inc(v_name_846_);
    leanh::lean_inc(v_keyName_847_);
    v___x_849_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_849_, 0, v_keyName_847_);
    leanh::lean_ctor_set(v___x_849_, 1, v_name_846_);
    v___x_850_ = l_Lake_Module_keyword;
    v___x_851_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_851_, 0, v___x_849_);
    leanh::lean_ctor_set(v___x_851_, 1, v___x_850_);
    leanh::lean_ctor_set(v___x_851_, 2, v_self_843_);
    leanh::lean_ctor_set(v___x_851_, 3, v___x_848_);
    return v___x_851_;
}
pub unsafe fn l_Lake_Module_deps(
    mut v_self_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_853_ = leanh::lean_ctor_get(v_self_852_, 0);
    v_pkg_854_ = leanh::lean_ctor_get(v_lib_853_, 0);
    v_name_855_ = leanh::lean_ctor_get(v_self_852_, 1);
    v_keyName_856_ = leanh::lean_ctor_get(v_pkg_854_, 2);
    v___x_857_ = l_Lake_Module_depsFacet;
    leanh::lean_inc(v_name_855_);
    leanh::lean_inc(v_keyName_856_);
    v___x_858_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_858_, 0, v_keyName_856_);
    leanh::lean_ctor_set(v___x_858_, 1, v_name_855_);
    v___x_859_ = l_Lake_Module_keyword;
    v___x_860_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_860_, 0, v___x_858_);
    leanh::lean_ctor_set(v___x_860_, 1, v___x_859_);
    leanh::lean_ctor_set(v___x_860_, 2, v_self_852_);
    leanh::lean_ctor_set(v___x_860_, 3, v___x_857_);
    return v___x_860_;
}
pub unsafe fn l_Lake_Module_importInfo(
    mut v_self_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_862_ = leanh::lean_ctor_get(v_self_861_, 0);
    v_pkg_863_ = leanh::lean_ctor_get(v_lib_862_, 0);
    v_name_864_ = leanh::lean_ctor_get(v_self_861_, 1);
    v_keyName_865_ = leanh::lean_ctor_get(v_pkg_863_, 2);
    v___x_866_ = l_Lake_Module_importInfoFacet;
    leanh::lean_inc(v_name_864_);
    leanh::lean_inc(v_keyName_865_);
    v___x_867_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_867_, 0, v_keyName_865_);
    leanh::lean_ctor_set(v___x_867_, 1, v_name_864_);
    v___x_868_ = l_Lake_Module_keyword;
    v___x_869_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_869_, 0, v___x_867_);
    leanh::lean_ctor_set(v___x_869_, 1, v___x_868_);
    leanh::lean_ctor_set(v___x_869_, 2, v_self_861_);
    leanh::lean_ctor_set(v___x_869_, 3, v___x_866_);
    return v___x_869_;
}
pub unsafe fn l_Lake_Module_exportInfo(
    mut v_self_870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_871_ = leanh::lean_ctor_get(v_self_870_, 0);
    v_pkg_872_ = leanh::lean_ctor_get(v_lib_871_, 0);
    v_name_873_ = leanh::lean_ctor_get(v_self_870_, 1);
    v_keyName_874_ = leanh::lean_ctor_get(v_pkg_872_, 2);
    v___x_875_ = l_Lake_Module_exportInfoFacet;
    leanh::lean_inc(v_name_873_);
    leanh::lean_inc(v_keyName_874_);
    v___x_876_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_876_, 0, v_keyName_874_);
    leanh::lean_ctor_set(v___x_876_, 1, v_name_873_);
    v___x_877_ = l_Lake_Module_keyword;
    v___x_878_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_878_, 0, v___x_876_);
    leanh::lean_ctor_set(v___x_878_, 1, v___x_877_);
    leanh::lean_ctor_set(v___x_878_, 2, v_self_870_);
    leanh::lean_ctor_set(v___x_878_, 3, v___x_875_);
    return v___x_878_;
}
pub unsafe fn l_Lake_Module_importArts(
    mut v_self_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_880_ = leanh::lean_ctor_get(v_self_879_, 0);
    v_pkg_881_ = leanh::lean_ctor_get(v_lib_880_, 0);
    v_name_882_ = leanh::lean_ctor_get(v_self_879_, 1);
    v_keyName_883_ = leanh::lean_ctor_get(v_pkg_881_, 2);
    v___x_884_ = l_Lake_Module_importArtsFacet;
    leanh::lean_inc(v_name_882_);
    leanh::lean_inc(v_keyName_883_);
    v___x_885_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_885_, 0, v_keyName_883_);
    leanh::lean_ctor_set(v___x_885_, 1, v_name_882_);
    v___x_886_ = l_Lake_Module_keyword;
    v___x_887_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_887_, 0, v___x_885_);
    leanh::lean_ctor_set(v___x_887_, 1, v___x_886_);
    leanh::lean_ctor_set(v___x_887_, 2, v_self_879_);
    leanh::lean_ctor_set(v___x_887_, 3, v___x_884_);
    return v___x_887_;
}
pub unsafe fn l_Lake_Module_importAllArts(
    mut v_self_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_889_ = leanh::lean_ctor_get(v_self_888_, 0);
    v_pkg_890_ = leanh::lean_ctor_get(v_lib_889_, 0);
    v_name_891_ = leanh::lean_ctor_get(v_self_888_, 1);
    v_keyName_892_ = leanh::lean_ctor_get(v_pkg_890_, 2);
    v___x_893_ = l_Lake_Module_importAllArtsFacet;
    leanh::lean_inc(v_name_891_);
    leanh::lean_inc(v_keyName_892_);
    v___x_894_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_894_, 0, v_keyName_892_);
    leanh::lean_ctor_set(v___x_894_, 1, v_name_891_);
    v___x_895_ = l_Lake_Module_keyword;
    v___x_896_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_896_, 0, v___x_894_);
    leanh::lean_ctor_set(v___x_896_, 1, v___x_895_);
    leanh::lean_ctor_set(v___x_896_, 2, v_self_888_);
    leanh::lean_ctor_set(v___x_896_, 3, v___x_893_);
    return v___x_896_;
}
pub unsafe fn l_Lake_Module_leanArts(
    mut v_self_897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_898_ = leanh::lean_ctor_get(v_self_897_, 0);
    v_pkg_899_ = leanh::lean_ctor_get(v_lib_898_, 0);
    v_name_900_ = leanh::lean_ctor_get(v_self_897_, 1);
    v_keyName_901_ = leanh::lean_ctor_get(v_pkg_899_, 2);
    v___x_902_ = l_Lake_Module_leanArtsFacet;
    leanh::lean_inc(v_name_900_);
    leanh::lean_inc(v_keyName_901_);
    v___x_903_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_903_, 0, v_keyName_901_);
    leanh::lean_ctor_set(v___x_903_, 1, v_name_900_);
    v___x_904_ = l_Lake_Module_keyword;
    v___x_905_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_905_, 0, v___x_903_);
    leanh::lean_ctor_set(v___x_905_, 1, v___x_904_);
    leanh::lean_ctor_set(v___x_905_, 2, v_self_897_);
    leanh::lean_ctor_set(v___x_905_, 3, v___x_902_);
    return v___x_905_;
}
pub unsafe fn l_Lake_Module_olean(
    mut v_self_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_907_ = leanh::lean_ctor_get(v_self_906_, 0);
    v_pkg_908_ = leanh::lean_ctor_get(v_lib_907_, 0);
    v_name_909_ = leanh::lean_ctor_get(v_self_906_, 1);
    v_keyName_910_ = leanh::lean_ctor_get(v_pkg_908_, 2);
    v___x_911_ = l_Lake_Module_oleanFacet;
    leanh::lean_inc(v_name_909_);
    leanh::lean_inc(v_keyName_910_);
    v___x_912_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_912_, 0, v_keyName_910_);
    leanh::lean_ctor_set(v___x_912_, 1, v_name_909_);
    v___x_913_ = l_Lake_Module_keyword;
    v___x_914_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_914_, 0, v___x_912_);
    leanh::lean_ctor_set(v___x_914_, 1, v___x_913_);
    leanh::lean_ctor_set(v___x_914_, 2, v_self_906_);
    leanh::lean_ctor_set(v___x_914_, 3, v___x_911_);
    return v___x_914_;
}
pub unsafe fn l_Lake_Module_oleanServer(
    mut v_self_915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_916_ = leanh::lean_ctor_get(v_self_915_, 0);
    v_pkg_917_ = leanh::lean_ctor_get(v_lib_916_, 0);
    v_name_918_ = leanh::lean_ctor_get(v_self_915_, 1);
    v_keyName_919_ = leanh::lean_ctor_get(v_pkg_917_, 2);
    v___x_920_ = l_Lake_Module_oleanServerFacet;
    leanh::lean_inc(v_name_918_);
    leanh::lean_inc(v_keyName_919_);
    v___x_921_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_921_, 0, v_keyName_919_);
    leanh::lean_ctor_set(v___x_921_, 1, v_name_918_);
    v___x_922_ = l_Lake_Module_keyword;
    v___x_923_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_923_, 0, v___x_921_);
    leanh::lean_ctor_set(v___x_923_, 1, v___x_922_);
    leanh::lean_ctor_set(v___x_923_, 2, v_self_915_);
    leanh::lean_ctor_set(v___x_923_, 3, v___x_920_);
    return v___x_923_;
}
pub unsafe fn l_Lake_Module_oleanPrivate(
    mut v_self_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_925_ = leanh::lean_ctor_get(v_self_924_, 0);
    v_pkg_926_ = leanh::lean_ctor_get(v_lib_925_, 0);
    v_name_927_ = leanh::lean_ctor_get(v_self_924_, 1);
    v_keyName_928_ = leanh::lean_ctor_get(v_pkg_926_, 2);
    v___x_929_ = l_Lake_Module_oleanPrivateFacet;
    leanh::lean_inc(v_name_927_);
    leanh::lean_inc(v_keyName_928_);
    v___x_930_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_930_, 0, v_keyName_928_);
    leanh::lean_ctor_set(v___x_930_, 1, v_name_927_);
    v___x_931_ = l_Lake_Module_keyword;
    v___x_932_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_932_, 0, v___x_930_);
    leanh::lean_ctor_set(v___x_932_, 1, v___x_931_);
    leanh::lean_ctor_set(v___x_932_, 2, v_self_924_);
    leanh::lean_ctor_set(v___x_932_, 3, v___x_929_);
    return v___x_932_;
}
pub unsafe fn l_Lake_Module_ilean(
    mut v_self_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_934_ = leanh::lean_ctor_get(v_self_933_, 0);
    v_pkg_935_ = leanh::lean_ctor_get(v_lib_934_, 0);
    v_name_936_ = leanh::lean_ctor_get(v_self_933_, 1);
    v_keyName_937_ = leanh::lean_ctor_get(v_pkg_935_, 2);
    v___x_938_ = l_Lake_Module_ileanFacet;
    leanh::lean_inc(v_name_936_);
    leanh::lean_inc(v_keyName_937_);
    v___x_939_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_939_, 0, v_keyName_937_);
    leanh::lean_ctor_set(v___x_939_, 1, v_name_936_);
    v___x_940_ = l_Lake_Module_keyword;
    v___x_941_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_941_, 0, v___x_939_);
    leanh::lean_ctor_set(v___x_941_, 1, v___x_940_);
    leanh::lean_ctor_set(v___x_941_, 2, v_self_933_);
    leanh::lean_ctor_set(v___x_941_, 3, v___x_938_);
    return v___x_941_;
}
pub unsafe fn l_Lake_Module_ir(
    mut v_self_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_943_ = leanh::lean_ctor_get(v_self_942_, 0);
    v_pkg_944_ = leanh::lean_ctor_get(v_lib_943_, 0);
    v_name_945_ = leanh::lean_ctor_get(v_self_942_, 1);
    v_keyName_946_ = leanh::lean_ctor_get(v_pkg_944_, 2);
    v___x_947_ = l_Lake_Module_irFacet;
    leanh::lean_inc(v_name_945_);
    leanh::lean_inc(v_keyName_946_);
    v___x_948_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_948_, 0, v_keyName_946_);
    leanh::lean_ctor_set(v___x_948_, 1, v_name_945_);
    v___x_949_ = l_Lake_Module_keyword;
    v___x_950_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_950_, 0, v___x_948_);
    leanh::lean_ctor_set(v___x_950_, 1, v___x_949_);
    leanh::lean_ctor_set(v___x_950_, 2, v_self_942_);
    leanh::lean_ctor_set(v___x_950_, 3, v___x_947_);
    return v___x_950_;
}
pub unsafe fn l_Lake_Module_c(
    mut v_self_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_952_ = leanh::lean_ctor_get(v_self_951_, 0);
    v_pkg_953_ = leanh::lean_ctor_get(v_lib_952_, 0);
    v_name_954_ = leanh::lean_ctor_get(v_self_951_, 1);
    v_keyName_955_ = leanh::lean_ctor_get(v_pkg_953_, 2);
    v___x_956_ = l_Lake_Module_cFacet;
    leanh::lean_inc(v_name_954_);
    leanh::lean_inc(v_keyName_955_);
    v___x_957_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_957_, 0, v_keyName_955_);
    leanh::lean_ctor_set(v___x_957_, 1, v_name_954_);
    v___x_958_ = l_Lake_Module_keyword;
    v___x_959_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_959_, 0, v___x_957_);
    leanh::lean_ctor_set(v___x_959_, 1, v___x_958_);
    leanh::lean_ctor_set(v___x_959_, 2, v_self_951_);
    leanh::lean_ctor_set(v___x_959_, 3, v___x_956_);
    return v___x_959_;
}
pub unsafe fn l_Lake_Module_bc(
    mut v_self_960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_961_ = leanh::lean_ctor_get(v_self_960_, 0);
    v_pkg_962_ = leanh::lean_ctor_get(v_lib_961_, 0);
    v_name_963_ = leanh::lean_ctor_get(v_self_960_, 1);
    v_keyName_964_ = leanh::lean_ctor_get(v_pkg_962_, 2);
    v___x_965_ = l_Lake_Module_bcFacet;
    leanh::lean_inc(v_name_963_);
    leanh::lean_inc(v_keyName_964_);
    v___x_966_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_966_, 0, v_keyName_964_);
    leanh::lean_ctor_set(v___x_966_, 1, v_name_963_);
    v___x_967_ = l_Lake_Module_keyword;
    v___x_968_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_968_, 0, v___x_966_);
    leanh::lean_ctor_set(v___x_968_, 1, v___x_967_);
    leanh::lean_ctor_set(v___x_968_, 2, v_self_960_);
    leanh::lean_ctor_set(v___x_968_, 3, v___x_965_);
    return v___x_968_;
}
pub unsafe fn l_Lake_Module_ltar(
    mut v_self_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_970_ = leanh::lean_ctor_get(v_self_969_, 0);
    v_pkg_971_ = leanh::lean_ctor_get(v_lib_970_, 0);
    v_name_972_ = leanh::lean_ctor_get(v_self_969_, 1);
    v_keyName_973_ = leanh::lean_ctor_get(v_pkg_971_, 2);
    v___x_974_ = l_Lake_Module_ltarFacet;
    leanh::lean_inc(v_name_972_);
    leanh::lean_inc(v_keyName_973_);
    v___x_975_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_975_, 0, v_keyName_973_);
    leanh::lean_ctor_set(v___x_975_, 1, v_name_972_);
    v___x_976_ = l_Lake_Module_keyword;
    v___x_977_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_977_, 0, v___x_975_);
    leanh::lean_ctor_set(v___x_977_, 1, v___x_976_);
    leanh::lean_ctor_set(v___x_977_, 2, v_self_969_);
    leanh::lean_ctor_set(v___x_977_, 3, v___x_974_);
    return v___x_977_;
}
pub unsafe fn l_Lake_Module_o(
    mut v_self_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_979_ = leanh::lean_ctor_get(v_self_978_, 0);
    v_pkg_980_ = leanh::lean_ctor_get(v_lib_979_, 0);
    v_name_981_ = leanh::lean_ctor_get(v_self_978_, 1);
    v_keyName_982_ = leanh::lean_ctor_get(v_pkg_980_, 2);
    v___x_983_ = l_Lake_Module_oFacet;
    leanh::lean_inc(v_name_981_);
    leanh::lean_inc(v_keyName_982_);
    v___x_984_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_984_, 0, v_keyName_982_);
    leanh::lean_ctor_set(v___x_984_, 1, v_name_981_);
    v___x_985_ = l_Lake_Module_keyword;
    v___x_986_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_986_, 0, v___x_984_);
    leanh::lean_ctor_set(v___x_986_, 1, v___x_985_);
    leanh::lean_ctor_set(v___x_986_, 2, v_self_978_);
    leanh::lean_ctor_set(v___x_986_, 3, v___x_983_);
    return v___x_986_;
}
pub unsafe fn l_Lake_Module_oExport(
    mut v_self_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_988_ = leanh::lean_ctor_get(v_self_987_, 0);
    v_pkg_989_ = leanh::lean_ctor_get(v_lib_988_, 0);
    v_name_990_ = leanh::lean_ctor_get(v_self_987_, 1);
    v_keyName_991_ = leanh::lean_ctor_get(v_pkg_989_, 2);
    v___x_992_ = l_Lake_Module_oExportFacet;
    leanh::lean_inc(v_name_990_);
    leanh::lean_inc(v_keyName_991_);
    v___x_993_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_993_, 0, v_keyName_991_);
    leanh::lean_ctor_set(v___x_993_, 1, v_name_990_);
    v___x_994_ = l_Lake_Module_keyword;
    v___x_995_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_995_, 0, v___x_993_);
    leanh::lean_ctor_set(v___x_995_, 1, v___x_994_);
    leanh::lean_ctor_set(v___x_995_, 2, v_self_987_);
    leanh::lean_ctor_set(v___x_995_, 3, v___x_992_);
    return v___x_995_;
}
pub unsafe fn l_Lake_Module_oNoExport(
    mut v_self_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_997_ = leanh::lean_ctor_get(v_self_996_, 0);
    v_pkg_998_ = leanh::lean_ctor_get(v_lib_997_, 0);
    v_name_999_ = leanh::lean_ctor_get(v_self_996_, 1);
    v_keyName_1000_ = leanh::lean_ctor_get(v_pkg_998_, 2);
    v___x_1001_ = l_Lake_Module_oNoExportFacet;
    leanh::lean_inc(v_name_999_);
    leanh::lean_inc(v_keyName_1000_);
    v___x_1002_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1002_, 0, v_keyName_1000_);
    leanh::lean_ctor_set(v___x_1002_, 1, v_name_999_);
    v___x_1003_ = l_Lake_Module_keyword;
    v___x_1004_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1004_, 0, v___x_1002_);
    leanh::lean_ctor_set(v___x_1004_, 1, v___x_1003_);
    leanh::lean_ctor_set(v___x_1004_, 2, v_self_996_);
    leanh::lean_ctor_set(v___x_1004_, 3, v___x_1001_);
    return v___x_1004_;
}
pub unsafe fn l_Lake_Module_co(
    mut v_self_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1006_ = leanh::lean_ctor_get(v_self_1005_, 0);
    v_pkg_1007_ = leanh::lean_ctor_get(v_lib_1006_, 0);
    v_name_1008_ = leanh::lean_ctor_get(v_self_1005_, 1);
    v_keyName_1009_ = leanh::lean_ctor_get(v_pkg_1007_, 2);
    v___x_1010_ = l_Lake_Module_coFacet;
    leanh::lean_inc(v_name_1008_);
    leanh::lean_inc(v_keyName_1009_);
    v___x_1011_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1011_, 0, v_keyName_1009_);
    leanh::lean_ctor_set(v___x_1011_, 1, v_name_1008_);
    v___x_1012_ = l_Lake_Module_keyword;
    v___x_1013_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1013_, 0, v___x_1011_);
    leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
    leanh::lean_ctor_set(v___x_1013_, 2, v_self_1005_);
    leanh::lean_ctor_set(v___x_1013_, 3, v___x_1010_);
    return v___x_1013_;
}
pub unsafe fn l_Lake_Module_coExport(
    mut v_self_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1015_ = leanh::lean_ctor_get(v_self_1014_, 0);
    v_pkg_1016_ = leanh::lean_ctor_get(v_lib_1015_, 0);
    v_name_1017_ = leanh::lean_ctor_get(v_self_1014_, 1);
    v_keyName_1018_ = leanh::lean_ctor_get(v_pkg_1016_, 2);
    v___x_1019_ = l_Lake_Module_coExportFacet;
    leanh::lean_inc(v_name_1017_);
    leanh::lean_inc(v_keyName_1018_);
    v___x_1020_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1020_, 0, v_keyName_1018_);
    leanh::lean_ctor_set(v___x_1020_, 1, v_name_1017_);
    v___x_1021_ = l_Lake_Module_keyword;
    v___x_1022_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1022_, 0, v___x_1020_);
    leanh::lean_ctor_set(v___x_1022_, 1, v___x_1021_);
    leanh::lean_ctor_set(v___x_1022_, 2, v_self_1014_);
    leanh::lean_ctor_set(v___x_1022_, 3, v___x_1019_);
    return v___x_1022_;
}
pub unsafe fn l_Lake_Module_coNoExport(
    mut v_self_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1024_ = leanh::lean_ctor_get(v_self_1023_, 0);
    v_pkg_1025_ = leanh::lean_ctor_get(v_lib_1024_, 0);
    v_name_1026_ = leanh::lean_ctor_get(v_self_1023_, 1);
    v_keyName_1027_ = leanh::lean_ctor_get(v_pkg_1025_, 2);
    v___x_1028_ = l_Lake_Module_coNoExportFacet;
    leanh::lean_inc(v_name_1026_);
    leanh::lean_inc(v_keyName_1027_);
    v___x_1029_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1029_, 0, v_keyName_1027_);
    leanh::lean_ctor_set(v___x_1029_, 1, v_name_1026_);
    v___x_1030_ = l_Lake_Module_keyword;
    v___x_1031_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1031_, 0, v___x_1029_);
    leanh::lean_ctor_set(v___x_1031_, 1, v___x_1030_);
    leanh::lean_ctor_set(v___x_1031_, 2, v_self_1023_);
    leanh::lean_ctor_set(v___x_1031_, 3, v___x_1028_);
    return v___x_1031_;
}
pub unsafe fn l_Lake_Module_bco(
    mut v_self_1032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1033_ = leanh::lean_ctor_get(v_self_1032_, 0);
    v_pkg_1034_ = leanh::lean_ctor_get(v_lib_1033_, 0);
    v_name_1035_ = leanh::lean_ctor_get(v_self_1032_, 1);
    v_keyName_1036_ = leanh::lean_ctor_get(v_pkg_1034_, 2);
    v___x_1037_ = l_Lake_Module_bcoFacet;
    leanh::lean_inc(v_name_1035_);
    leanh::lean_inc(v_keyName_1036_);
    v___x_1038_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1038_, 0, v_keyName_1036_);
    leanh::lean_ctor_set(v___x_1038_, 1, v_name_1035_);
    v___x_1039_ = l_Lake_Module_keyword;
    v___x_1040_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1040_, 0, v___x_1038_);
    leanh::lean_ctor_set(v___x_1040_, 1, v___x_1039_);
    leanh::lean_ctor_set(v___x_1040_, 2, v_self_1032_);
    leanh::lean_ctor_set(v___x_1040_, 3, v___x_1037_);
    return v___x_1040_;
}
pub unsafe fn l_Lake_Module_dynlib(
    mut v_self_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1042_ = leanh::lean_ctor_get(v_self_1041_, 0);
    v_pkg_1043_ = leanh::lean_ctor_get(v_lib_1042_, 0);
    v_name_1044_ = leanh::lean_ctor_get(v_self_1041_, 1);
    v_keyName_1045_ = leanh::lean_ctor_get(v_pkg_1043_, 2);
    v___x_1046_ = l_Lake_Module_dynlibFacet;
    leanh::lean_inc(v_name_1044_);
    leanh::lean_inc(v_keyName_1045_);
    v___x_1047_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1047_, 0, v_keyName_1045_);
    leanh::lean_ctor_set(v___x_1047_, 1, v_name_1044_);
    v___x_1048_ = l_Lake_Module_keyword;
    v___x_1049_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1049_, 0, v___x_1047_);
    leanh::lean_ctor_set(v___x_1049_, 1, v___x_1048_);
    leanh::lean_ctor_set(v___x_1049_, 2, v_self_1041_);
    leanh::lean_ctor_set(v___x_1049_, 3, v___x_1046_);
    return v___x_1049_;
}
pub unsafe fn l_Lake_Package_target(
    mut v_target_1050_: *mut leanh::LeanObject,
    mut v_self_1051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1052_, 0, v_self_1051_);
    leanh::lean_ctor_set(v___x_1052_, 1, v_target_1050_);
    return v___x_1052_;
}
pub unsafe fn l_Lake_Package_facetCore(
    mut v_facet_1053_: *mut leanh::LeanObject,
    mut v_self_1054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1055_ = leanh::lean_ctor_get(v_self_1054_, 2);
    leanh::lean_inc(v_keyName_1055_);
    v___x_1056_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1056_, 0, v_keyName_1055_);
    v___x_1057_ = l_Lake_Package_keyword;
    v___x_1058_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1058_, 0, v___x_1056_);
    leanh::lean_ctor_set(v___x_1058_, 1, v___x_1057_);
    leanh::lean_ctor_set(v___x_1058_, 2, v_self_1054_);
    leanh::lean_ctor_set(v___x_1058_, 3, v_facet_1053_);
    return v___x_1058_;
}
pub unsafe fn l_Lake_Package_facet(
    mut v_facet_1059_: *mut leanh::LeanObject,
    mut v_self_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1061_ = leanh::lean_ctor_get(v_self_1060_, 2);
    v___x_1062_ = l_Lake_Package_keyword;
    v___x_1063_ = l_Lean_Name_append(v___x_1062_, v_facet_1059_);
    leanh::lean_inc(v_keyName_1061_);
    v___x_1064_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1064_, 0, v_keyName_1061_);
    v___x_1065_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1065_, 0, v___x_1064_);
    leanh::lean_ctor_set(v___x_1065_, 1, v___x_1062_);
    leanh::lean_ctor_set(v___x_1065_, 2, v_self_1060_);
    leanh::lean_ctor_set(v___x_1065_, 3, v___x_1063_);
    return v___x_1065_;
}
pub unsafe fn l_Lake_Package_buildCache(
    mut v_self_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1067_ = leanh::lean_ctor_get(v_self_1066_, 2);
    v___x_1068_ = l_Lake_Package_buildCacheFacet;
    leanh::lean_inc(v_keyName_1067_);
    v___x_1069_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1069_, 0, v_keyName_1067_);
    v___x_1070_ = l_Lake_Package_keyword;
    v___x_1071_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1071_, 0, v___x_1069_);
    leanh::lean_ctor_set(v___x_1071_, 1, v___x_1070_);
    leanh::lean_ctor_set(v___x_1071_, 2, v_self_1066_);
    leanh::lean_ctor_set(v___x_1071_, 3, v___x_1068_);
    return v___x_1071_;
}
pub unsafe fn l_Lake_Package_optBuildCache(
    mut v_self_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1073_ = leanh::lean_ctor_get(v_self_1072_, 2);
    v___x_1074_ = l_Lake_Package_optBuildCacheFacet;
    leanh::lean_inc(v_keyName_1073_);
    v___x_1075_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1075_, 0, v_keyName_1073_);
    v___x_1076_ = l_Lake_Package_keyword;
    v___x_1077_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1077_, 0, v___x_1075_);
    leanh::lean_ctor_set(v___x_1077_, 1, v___x_1076_);
    leanh::lean_ctor_set(v___x_1077_, 2, v_self_1072_);
    leanh::lean_ctor_set(v___x_1077_, 3, v___x_1074_);
    return v___x_1077_;
}
pub unsafe fn l_Lake_Package_reservoirBarrel(
    mut v_self_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1079_ = leanh::lean_ctor_get(v_self_1078_, 2);
    v___x_1080_ = l_Lake_Package_reservoirBarrelFacet;
    leanh::lean_inc(v_keyName_1079_);
    v___x_1081_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1081_, 0, v_keyName_1079_);
    v___x_1082_ = l_Lake_Package_keyword;
    v___x_1083_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1083_, 0, v___x_1081_);
    leanh::lean_ctor_set(v___x_1083_, 1, v___x_1082_);
    leanh::lean_ctor_set(v___x_1083_, 2, v_self_1078_);
    leanh::lean_ctor_set(v___x_1083_, 3, v___x_1080_);
    return v___x_1083_;
}
pub unsafe fn l_Lake_Package_optReservoirBarrel(
    mut v_self_1084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1085_ = leanh::lean_ctor_get(v_self_1084_, 2);
    v___x_1086_ = l_Lake_Package_optReservoirBarrelFacet;
    leanh::lean_inc(v_keyName_1085_);
    v___x_1087_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1087_, 0, v_keyName_1085_);
    v___x_1088_ = l_Lake_Package_keyword;
    v___x_1089_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1089_, 0, v___x_1087_);
    leanh::lean_ctor_set(v___x_1089_, 1, v___x_1088_);
    leanh::lean_ctor_set(v___x_1089_, 2, v_self_1084_);
    leanh::lean_ctor_set(v___x_1089_, 3, v___x_1086_);
    return v___x_1089_;
}
pub unsafe fn l_Lake_Package_gitHubRelease(
    mut v_self_1090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1091_ = leanh::lean_ctor_get(v_self_1090_, 2);
    v___x_1092_ = l_Lake_Package_gitHubReleaseFacet;
    leanh::lean_inc(v_keyName_1091_);
    v___x_1093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1093_, 0, v_keyName_1091_);
    v___x_1094_ = l_Lake_Package_keyword;
    v___x_1095_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1095_, 0, v___x_1093_);
    leanh::lean_ctor_set(v___x_1095_, 1, v___x_1094_);
    leanh::lean_ctor_set(v___x_1095_, 2, v_self_1090_);
    leanh::lean_ctor_set(v___x_1095_, 3, v___x_1092_);
    return v___x_1095_;
}
pub unsafe fn l_Lake_Package_optGitHubRelease(
    mut v_self_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1097_ = leanh::lean_ctor_get(v_self_1096_, 2);
    v___x_1098_ = l_Lake_Package_optGitHubReleaseFacet;
    leanh::lean_inc(v_keyName_1097_);
    v___x_1099_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1099_, 0, v_keyName_1097_);
    v___x_1100_ = l_Lake_Package_keyword;
    v___x_1101_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1101_, 0, v___x_1099_);
    leanh::lean_ctor_set(v___x_1101_, 1, v___x_1100_);
    leanh::lean_ctor_set(v___x_1101_, 2, v_self_1096_);
    leanh::lean_ctor_set(v___x_1101_, 3, v___x_1098_);
    return v___x_1101_;
}
pub unsafe fn l_Lake_Package_extraDep(
    mut v_self_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1103_ = leanh::lean_ctor_get(v_self_1102_, 2);
    v___x_1104_ = l_Lake_Package_extraDepFacet;
    leanh::lean_inc(v_keyName_1103_);
    v___x_1105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1105_, 0, v_keyName_1103_);
    v___x_1106_ = l_Lake_Package_keyword;
    v___x_1107_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1107_, 0, v___x_1105_);
    leanh::lean_ctor_set(v___x_1107_, 1, v___x_1106_);
    leanh::lean_ctor_set(v___x_1107_, 2, v_self_1102_);
    leanh::lean_ctor_set(v___x_1107_, 3, v___x_1104_);
    return v___x_1107_;
}
pub unsafe fn l_Lake_Package_deps(
    mut v_self_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1109_ = leanh::lean_ctor_get(v_self_1108_, 2);
    v___x_1110_ = l_Lake_Package_depsFacet;
    leanh::lean_inc(v_keyName_1109_);
    v___x_1111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1111_, 0, v_keyName_1109_);
    v___x_1112_ = l_Lake_Package_keyword;
    v___x_1113_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1113_, 0, v___x_1111_);
    leanh::lean_ctor_set(v___x_1113_, 1, v___x_1112_);
    leanh::lean_ctor_set(v___x_1113_, 2, v_self_1108_);
    leanh::lean_ctor_set(v___x_1113_, 3, v___x_1110_);
    return v___x_1113_;
}
pub unsafe fn l_Lake_Package_transDeps(
    mut v_self_1114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyName_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1115_ = leanh::lean_ctor_get(v_self_1114_, 2);
    v___x_1116_ = l_Lake_Package_transDepsFacet;
    leanh::lean_inc(v_keyName_1115_);
    v___x_1117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1117_, 0, v_keyName_1115_);
    v___x_1118_ = l_Lake_Package_keyword;
    v___x_1119_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1119_, 0, v___x_1117_);
    leanh::lean_ctor_set(v___x_1119_, 1, v___x_1118_);
    leanh::lean_ctor_set(v___x_1119_, 2, v_self_1114_);
    leanh::lean_ctor_set(v___x_1119_, 3, v___x_1116_);
    return v___x_1119_;
}
pub unsafe fn l_Lake_LeanLib_facetCore(
    mut v_facet_1120_: *mut leanh::LeanObject,
    mut v_self_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1122_ = leanh::lean_ctor_get(v_self_1121_, 0);
    v_name_1123_ = leanh::lean_ctor_get(v_self_1121_, 1);
    v_keyName_1124_ = leanh::lean_ctor_get(v_pkg_1122_, 2);
    leanh::lean_inc(v_name_1123_);
    leanh::lean_inc(v_keyName_1124_);
    v___x_1125_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1125_, 0, v_keyName_1124_);
    leanh::lean_ctor_set(v___x_1125_, 1, v_name_1123_);
    v___x_1126_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1127_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1127_, 0, v___x_1125_);
    leanh::lean_ctor_set(v___x_1127_, 1, v___x_1126_);
    leanh::lean_ctor_set(v___x_1127_, 2, v_self_1121_);
    leanh::lean_ctor_set(v___x_1127_, 3, v_facet_1120_);
    return v___x_1127_;
}
pub unsafe fn l_Lake_LeanLib_facet(
    mut v_facet_1128_: *mut leanh::LeanObject,
    mut v_self_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1130_ = leanh::lean_ctor_get(v_self_1129_, 0);
    v_name_1131_ = leanh::lean_ctor_get(v_self_1129_, 1);
    v_keyName_1132_ = leanh::lean_ctor_get(v_pkg_1130_, 2);
    v___x_1133_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1134_ = l_Lean_Name_append(v___x_1133_, v_facet_1128_);
    leanh::lean_inc(v_name_1131_);
    leanh::lean_inc(v_keyName_1132_);
    v___x_1135_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1135_, 0, v_keyName_1132_);
    leanh::lean_ctor_set(v___x_1135_, 1, v_name_1131_);
    v___x_1136_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1136_, 0, v___x_1135_);
    leanh::lean_ctor_set(v___x_1136_, 1, v___x_1133_);
    leanh::lean_ctor_set(v___x_1136_, 2, v_self_1129_);
    leanh::lean_ctor_set(v___x_1136_, 3, v___x_1134_);
    return v___x_1136_;
}
pub unsafe fn l_Lake_LeanLib_default(
    mut v_self_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1138_ = leanh::lean_ctor_get(v_self_1137_, 0);
    v_name_1139_ = leanh::lean_ctor_get(v_self_1137_, 1);
    v_keyName_1140_ = leanh::lean_ctor_get(v_pkg_1138_, 2);
    v___x_1141_ = l_Lake_LeanLib_defaultFacet;
    leanh::lean_inc(v_name_1139_);
    leanh::lean_inc(v_keyName_1140_);
    v___x_1142_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1142_, 0, v_keyName_1140_);
    leanh::lean_ctor_set(v___x_1142_, 1, v_name_1139_);
    v___x_1143_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1144_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1144_, 0, v___x_1142_);
    leanh::lean_ctor_set(v___x_1144_, 1, v___x_1143_);
    leanh::lean_ctor_set(v___x_1144_, 2, v_self_1137_);
    leanh::lean_ctor_set(v___x_1144_, 3, v___x_1141_);
    return v___x_1144_;
}
pub unsafe fn l_Lake_LeanLib_modules(
    mut v_self_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1146_ = leanh::lean_ctor_get(v_self_1145_, 0);
    v_name_1147_ = leanh::lean_ctor_get(v_self_1145_, 1);
    v_keyName_1148_ = leanh::lean_ctor_get(v_pkg_1146_, 2);
    v___x_1149_ = l_Lake_LeanLib_modulesFacet;
    leanh::lean_inc(v_name_1147_);
    leanh::lean_inc(v_keyName_1148_);
    v___x_1150_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1150_, 0, v_keyName_1148_);
    leanh::lean_ctor_set(v___x_1150_, 1, v_name_1147_);
    v___x_1151_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1152_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1152_, 0, v___x_1150_);
    leanh::lean_ctor_set(v___x_1152_, 1, v___x_1151_);
    leanh::lean_ctor_set(v___x_1152_, 2, v_self_1145_);
    leanh::lean_ctor_set(v___x_1152_, 3, v___x_1149_);
    return v___x_1152_;
}
pub unsafe fn l_Lake_LeanLib_leanArts(
    mut v_self_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1154_ = leanh::lean_ctor_get(v_self_1153_, 0);
    v_name_1155_ = leanh::lean_ctor_get(v_self_1153_, 1);
    v_keyName_1156_ = leanh::lean_ctor_get(v_pkg_1154_, 2);
    v___x_1157_ = l_Lake_LeanLib_leanArtsFacet;
    leanh::lean_inc(v_name_1155_);
    leanh::lean_inc(v_keyName_1156_);
    v___x_1158_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1158_, 0, v_keyName_1156_);
    leanh::lean_ctor_set(v___x_1158_, 1, v_name_1155_);
    v___x_1159_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1160_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1160_, 0, v___x_1158_);
    leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    leanh::lean_ctor_set(v___x_1160_, 2, v_self_1153_);
    leanh::lean_ctor_set(v___x_1160_, 3, v___x_1157_);
    return v___x_1160_;
}
pub unsafe fn l_Lake_LeanLib_static(
    mut v_self_1161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1162_ = leanh::lean_ctor_get(v_self_1161_, 0);
    v_name_1163_ = leanh::lean_ctor_get(v_self_1161_, 1);
    v_keyName_1164_ = leanh::lean_ctor_get(v_pkg_1162_, 2);
    v___x_1165_ = l_Lake_LeanLib_staticFacet;
    leanh::lean_inc(v_name_1163_);
    leanh::lean_inc(v_keyName_1164_);
    v___x_1166_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1166_, 0, v_keyName_1164_);
    leanh::lean_ctor_set(v___x_1166_, 1, v_name_1163_);
    v___x_1167_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1168_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1168_, 0, v___x_1166_);
    leanh::lean_ctor_set(v___x_1168_, 1, v___x_1167_);
    leanh::lean_ctor_set(v___x_1168_, 2, v_self_1161_);
    leanh::lean_ctor_set(v___x_1168_, 3, v___x_1165_);
    return v___x_1168_;
}
pub unsafe fn l_Lake_LeanLib_staticExport(
    mut v_self_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1170_ = leanh::lean_ctor_get(v_self_1169_, 0);
    v_name_1171_ = leanh::lean_ctor_get(v_self_1169_, 1);
    v_keyName_1172_ = leanh::lean_ctor_get(v_pkg_1170_, 2);
    v___x_1173_ = l_Lake_LeanLib_staticExportFacet;
    leanh::lean_inc(v_name_1171_);
    leanh::lean_inc(v_keyName_1172_);
    v___x_1174_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1174_, 0, v_keyName_1172_);
    leanh::lean_ctor_set(v___x_1174_, 1, v_name_1171_);
    v___x_1175_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1176_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1176_, 0, v___x_1174_);
    leanh::lean_ctor_set(v___x_1176_, 1, v___x_1175_);
    leanh::lean_ctor_set(v___x_1176_, 2, v_self_1169_);
    leanh::lean_ctor_set(v___x_1176_, 3, v___x_1173_);
    return v___x_1176_;
}
pub unsafe fn l_Lake_LeanLib_shared(
    mut v_self_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1178_ = leanh::lean_ctor_get(v_self_1177_, 0);
    v_name_1179_ = leanh::lean_ctor_get(v_self_1177_, 1);
    v_keyName_1180_ = leanh::lean_ctor_get(v_pkg_1178_, 2);
    v___x_1181_ = l_Lake_LeanLib_sharedFacet;
    leanh::lean_inc(v_name_1179_);
    leanh::lean_inc(v_keyName_1180_);
    v___x_1182_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1182_, 0, v_keyName_1180_);
    leanh::lean_ctor_set(v___x_1182_, 1, v_name_1179_);
    v___x_1183_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1184_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1184_, 0, v___x_1182_);
    leanh::lean_ctor_set(v___x_1184_, 1, v___x_1183_);
    leanh::lean_ctor_set(v___x_1184_, 2, v_self_1177_);
    leanh::lean_ctor_set(v___x_1184_, 3, v___x_1181_);
    return v___x_1184_;
}
pub unsafe fn l_Lake_LeanLib_extraDep(
    mut v_self_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1186_ = leanh::lean_ctor_get(v_self_1185_, 0);
    v_name_1187_ = leanh::lean_ctor_get(v_self_1185_, 1);
    v_keyName_1188_ = leanh::lean_ctor_get(v_pkg_1186_, 2);
    v___x_1189_ = l_Lake_LeanLib_extraDepFacet;
    leanh::lean_inc(v_name_1187_);
    leanh::lean_inc(v_keyName_1188_);
    v___x_1190_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1190_, 0, v_keyName_1188_);
    leanh::lean_ctor_set(v___x_1190_, 1, v_name_1187_);
    v___x_1191_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1192_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1192_, 0, v___x_1190_);
    leanh::lean_ctor_set(v___x_1192_, 1, v___x_1191_);
    leanh::lean_ctor_set(v___x_1192_, 2, v_self_1185_);
    leanh::lean_ctor_set(v___x_1192_, 3, v___x_1189_);
    return v___x_1192_;
}
pub unsafe fn l_Lake_LeanExe_facetCore(
    mut v_facet_1193_: *mut leanh::LeanObject,
    mut v_self_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1195_ = leanh::lean_ctor_get(v_self_1194_, 0);
    v_name_1196_ = leanh::lean_ctor_get(v_self_1194_, 1);
    v_keyName_1197_ = leanh::lean_ctor_get(v_pkg_1195_, 2);
    leanh::lean_inc(v_name_1196_);
    leanh::lean_inc(v_keyName_1197_);
    v___x_1198_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1198_, 0, v_keyName_1197_);
    leanh::lean_ctor_set(v___x_1198_, 1, v_name_1196_);
    v___x_1199_ = l_Lake_LeanExe_keyword;
    v___x_1200_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1200_, 0, v___x_1198_);
    leanh::lean_ctor_set(v___x_1200_, 1, v___x_1199_);
    leanh::lean_ctor_set(v___x_1200_, 2, v_self_1194_);
    leanh::lean_ctor_set(v___x_1200_, 3, v_facet_1193_);
    return v___x_1200_;
}
pub unsafe fn l_Lake_LeanExe_exe(
    mut v_self_1201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1202_ = leanh::lean_ctor_get(v_self_1201_, 0);
    v_name_1203_ = leanh::lean_ctor_get(v_self_1201_, 1);
    v_keyName_1204_ = leanh::lean_ctor_get(v_pkg_1202_, 2);
    v___x_1205_ = l_Lake_LeanExe_exeFacet;
    leanh::lean_inc(v_name_1203_);
    leanh::lean_inc(v_keyName_1204_);
    v___x_1206_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1206_, 0, v_keyName_1204_);
    leanh::lean_ctor_set(v___x_1206_, 1, v_name_1203_);
    v___x_1207_ = l_Lake_LeanExe_keyword;
    v___x_1208_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1208_, 0, v___x_1206_);
    leanh::lean_ctor_set(v___x_1208_, 1, v___x_1207_);
    leanh::lean_ctor_set(v___x_1208_, 2, v_self_1201_);
    leanh::lean_ctor_set(v___x_1208_, 3, v___x_1205_);
    return v___x_1208_;
}
pub unsafe fn l_Lake_ExternLib_facetCore(
    mut v_facet_1209_: *mut leanh::LeanObject,
    mut v_self_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1211_ = leanh::lean_ctor_get(v_self_1210_, 0);
    v_name_1212_ = leanh::lean_ctor_get(v_self_1210_, 1);
    v_keyName_1213_ = leanh::lean_ctor_get(v_pkg_1211_, 2);
    leanh::lean_inc(v_name_1212_);
    leanh::lean_inc(v_keyName_1213_);
    v___x_1214_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1214_, 0, v_keyName_1213_);
    leanh::lean_ctor_set(v___x_1214_, 1, v_name_1212_);
    v___x_1215_ = l_Lake_ExternLib_keyword;
    v___x_1216_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1216_, 0, v___x_1214_);
    leanh::lean_ctor_set(v___x_1216_, 1, v___x_1215_);
    leanh::lean_ctor_set(v___x_1216_, 2, v_self_1210_);
    leanh::lean_ctor_set(v___x_1216_, 3, v_facet_1209_);
    return v___x_1216_;
}
pub unsafe fn l_Lake_ExternLib_static(
    mut v_self_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1218_ = leanh::lean_ctor_get(v_self_1217_, 0);
    v_name_1219_ = leanh::lean_ctor_get(v_self_1217_, 1);
    v_keyName_1220_ = leanh::lean_ctor_get(v_pkg_1218_, 2);
    v___x_1221_ = l_Lake_ExternLib_staticFacet;
    leanh::lean_inc(v_name_1219_);
    leanh::lean_inc(v_keyName_1220_);
    v___x_1222_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1222_, 0, v_keyName_1220_);
    leanh::lean_ctor_set(v___x_1222_, 1, v_name_1219_);
    v___x_1223_ = l_Lake_ExternLib_keyword;
    v___x_1224_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1224_, 0, v___x_1222_);
    leanh::lean_ctor_set(v___x_1224_, 1, v___x_1223_);
    leanh::lean_ctor_set(v___x_1224_, 2, v_self_1217_);
    leanh::lean_ctor_set(v___x_1224_, 3, v___x_1221_);
    return v___x_1224_;
}
pub unsafe fn l_Lake_ExternLib_shared(
    mut v_self_1225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1226_ = leanh::lean_ctor_get(v_self_1225_, 0);
    v_name_1227_ = leanh::lean_ctor_get(v_self_1225_, 1);
    v_keyName_1228_ = leanh::lean_ctor_get(v_pkg_1226_, 2);
    v___x_1229_ = l_Lake_ExternLib_sharedFacet;
    leanh::lean_inc(v_name_1227_);
    leanh::lean_inc(v_keyName_1228_);
    v___x_1230_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1230_, 0, v_keyName_1228_);
    leanh::lean_ctor_set(v___x_1230_, 1, v_name_1227_);
    v___x_1231_ = l_Lake_ExternLib_keyword;
    v___x_1232_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1232_, 0, v___x_1230_);
    leanh::lean_ctor_set(v___x_1232_, 1, v___x_1231_);
    leanh::lean_ctor_set(v___x_1232_, 2, v_self_1225_);
    leanh::lean_ctor_set(v___x_1232_, 3, v___x_1229_);
    return v___x_1232_;
}
pub unsafe fn l_Lake_ExternLib_dynlib(
    mut v_self_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1234_ = leanh::lean_ctor_get(v_self_1233_, 0);
    v_name_1235_ = leanh::lean_ctor_get(v_self_1233_, 1);
    v_keyName_1236_ = leanh::lean_ctor_get(v_pkg_1234_, 2);
    v___x_1237_ = l_Lake_ExternLib_dynlibFacet;
    leanh::lean_inc(v_name_1235_);
    leanh::lean_inc(v_keyName_1236_);
    v___x_1238_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1238_, 0, v_keyName_1236_);
    leanh::lean_ctor_set(v___x_1238_, 1, v_name_1235_);
    v___x_1239_ = l_Lake_ExternLib_keyword;
    v___x_1240_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1240_, 0, v___x_1238_);
    leanh::lean_ctor_set(v___x_1240_, 1, v___x_1239_);
    leanh::lean_ctor_set(v___x_1240_, 2, v_self_1233_);
    leanh::lean_ctor_set(v___x_1240_, 3, v___x_1237_);
    return v___x_1240_;
}
pub unsafe fn l_Lake_InputFile_facetCore(
    mut v_facet_1241_: *mut leanh::LeanObject,
    mut v_self_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1243_ = leanh::lean_ctor_get(v_self_1242_, 0);
    v_name_1244_ = leanh::lean_ctor_get(v_self_1242_, 1);
    v_keyName_1245_ = leanh::lean_ctor_get(v_pkg_1243_, 2);
    leanh::lean_inc(v_name_1244_);
    leanh::lean_inc(v_keyName_1245_);
    v___x_1246_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1246_, 0, v_keyName_1245_);
    leanh::lean_ctor_set(v___x_1246_, 1, v_name_1244_);
    v___x_1247_ = l_Lake_InputFile_keyword;
    v___x_1248_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1248_, 0, v___x_1246_);
    leanh::lean_ctor_set(v___x_1248_, 1, v___x_1247_);
    leanh::lean_ctor_set(v___x_1248_, 2, v_self_1242_);
    leanh::lean_ctor_set(v___x_1248_, 3, v_facet_1241_);
    return v___x_1248_;
}
pub unsafe fn l_Lake_InputFile_default(
    mut v_self_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1250_ = leanh::lean_ctor_get(v_self_1249_, 0);
    v_name_1251_ = leanh::lean_ctor_get(v_self_1249_, 1);
    v_keyName_1252_ = leanh::lean_ctor_get(v_pkg_1250_, 2);
    v___x_1253_ = l_Lake_InputFile_defaultFacet;
    leanh::lean_inc(v_name_1251_);
    leanh::lean_inc(v_keyName_1252_);
    v___x_1254_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1254_, 0, v_keyName_1252_);
    leanh::lean_ctor_set(v___x_1254_, 1, v_name_1251_);
    v___x_1255_ = l_Lake_InputFile_keyword;
    v___x_1256_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1256_, 0, v___x_1254_);
    leanh::lean_ctor_set(v___x_1256_, 1, v___x_1255_);
    leanh::lean_ctor_set(v___x_1256_, 2, v_self_1249_);
    leanh::lean_ctor_set(v___x_1256_, 3, v___x_1253_);
    return v___x_1256_;
}
pub unsafe fn l_Lake_InputDir_facetCore(
    mut v_facet_1257_: *mut leanh::LeanObject,
    mut v_self_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1259_ = leanh::lean_ctor_get(v_self_1258_, 0);
    v_name_1260_ = leanh::lean_ctor_get(v_self_1258_, 1);
    v_keyName_1261_ = leanh::lean_ctor_get(v_pkg_1259_, 2);
    leanh::lean_inc(v_name_1260_);
    leanh::lean_inc(v_keyName_1261_);
    v___x_1262_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1262_, 0, v_keyName_1261_);
    leanh::lean_ctor_set(v___x_1262_, 1, v_name_1260_);
    v___x_1263_ = l_Lake_InputDir_keyword;
    v___x_1264_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1264_, 0, v___x_1262_);
    leanh::lean_ctor_set(v___x_1264_, 1, v___x_1263_);
    leanh::lean_ctor_set(v___x_1264_, 2, v_self_1258_);
    leanh::lean_ctor_set(v___x_1264_, 3, v_facet_1257_);
    return v___x_1264_;
}
pub unsafe fn l_Lake_InputDir_default(
    mut v_self_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pkg_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pkg_1266_ = leanh::lean_ctor_get(v_self_1265_, 0);
    v_name_1267_ = leanh::lean_ctor_get(v_self_1265_, 1);
    v_keyName_1268_ = leanh::lean_ctor_get(v_pkg_1266_, 2);
    v___x_1269_ = l_Lake_InputDir_defaultFacet;
    leanh::lean_inc(v_name_1267_);
    leanh::lean_inc(v_keyName_1268_);
    v___x_1270_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1270_, 0, v_keyName_1268_);
    leanh::lean_ctor_set(v___x_1270_, 1, v_name_1267_);
    v___x_1271_ = l_Lake_InputDir_keyword;
    v___x_1272_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1272_, 0, v___x_1270_);
    leanh::lean_ctor_set(v___x_1272_, 1, v___x_1271_);
    leanh::lean_ctor_set(v___x_1272_, 2, v_self_1265_);
    leanh::lean_ctor_set(v___x_1272_, 3, v___x_1269_);
    return v___x_1272_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Infos(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Info(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Infos(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Build_Data(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Infos(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Info(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LeanExe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_ExternLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_InputFile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Data(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Infos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Infos(builtin);
}