// Lean compiler output
// Module: Lake.Build.Infos
// Imports: Lake.Build.Info Lake.Config.LeanExe Lake.Config.ExternLib Lake.Config.InputFile Lake.Build.Data
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lake::Build::Data::{
    initialize_Lake_Build_Data, meta_initialize_Lake_Build_Data,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive,
};
pub static l_Lake_instDataKindModule___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_instDataKindModule___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindModule___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value) as *mut LeanObject,
        5134674735115079031 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindModule___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindModule: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindModule___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindPackage___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_instDataKindPackage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindPackage___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value) as *mut LeanObject,
        6671755061125946191 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindPackage___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindPackage: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindLeanLib___closed__0_value: LeanStringObject<9> = LeanStringObject {
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
static mut l_Lake_instDataKindLeanLib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindLeanLib___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value) as *mut LeanObject,
        12295998048739818339 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindLeanLib___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindLeanLib: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindLeanExe___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_instDataKindLeanExe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindLeanExe___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__0_value) as *mut LeanObject,
        10587356296225942211 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindLeanExe___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindLeanExe: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindLeanExe___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindExternLib___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instDataKindExternLib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindExternLib___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__0_value) as *mut LeanObject,
        11562366611225967008 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindExternLib___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindExternLib: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindExternLib___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindInputFile___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instDataKindInputFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindInputFile___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__0_value) as *mut LeanObject,
        4067501922346325234 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindInputFile___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindInputFile: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputFile___closed__1_value) as *mut LeanObject;
pub static l_Lake_instDataKindInputDir___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_instDataKindInputDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDataKindInputDir___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__0_value) as *mut LeanObject,
        9710019104504222840 as *mut LeanObject,
    ],
};
static mut l_Lake_instDataKindInputDir___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instDataKindInputDir: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDataKindInputDir___closed__1_value) as *mut LeanObject;
pub static l_Lake_Module_inputFacet___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Module_inputFacet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__0_value) as *mut LeanObject;
static l_Lake_Module_inputFacet___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value) as *mut LeanObject,
        5134674735115079031 as *mut LeanObject,
    ],
};
pub static l_Lake_Module_inputFacet___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__0_value) as *mut LeanObject,
        14553655559741226012 as *mut LeanObject,
    ],
};
static mut l_Lake_Module_inputFacet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Module_inputFacet: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_inputFacet___closed__1_value) as *mut LeanObject;
pub static l_Lake_Module_importsFacet___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Module_importsFacet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__0_value) as *mut LeanObject;
static l_Lake_Module_importsFacet___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value) as *mut LeanObject,
        5134674735115079031 as *mut LeanObject,
    ],
};
pub static l_Lake_Module_importsFacet___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__0_value) as *mut LeanObject,
        6906776088522269727 as *mut LeanObject,
    ],
};
static mut l_Lake_Module_importsFacet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Module_importsFacet: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importsFacet___closed__1_value) as *mut LeanObject;
pub static l_Lake_Module_transImportsFacet___closed__0_value: LeanStringObject<13> =
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
        m_data: [116, 114, 97, 110, 115, 73, 109, 112, 111, 114, 116, 115, 0],
    };
static mut l_Lake_Module_transImportsFacet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__0_value) as *mut LeanObject;
static l_Lake_Module_transImportsFacet___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value) as *mut LeanObject,
            5134674735115079031 as *mut LeanObject,
        ],
    };
pub static l_Lake_Module_transImportsFacet___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__0_value) as *mut LeanObject,
        15145167986846249592 as *mut LeanObject,
    ],
};
static mut l_Lake_Module_transImportsFacet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Module_transImportsFacet: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_transImportsFacet___closed__1_value) as *mut LeanObject;
pub static l_Lake_Module_precompileImportsFacet___closed__0_value: LeanStringObject<18> =
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
            112, 114, 101, 99, 111, 109, 112, 105, 108, 101, 73, 109, 112, 111, 114, 116, 115, 0,
        ],
    };
static mut l_Lake_Module_precompileImportsFacet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__0_value) as *mut LeanObject;
static l_Lake_Module_precompileImportsFacet___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value) as *mut LeanObject,
            5134674735115079031 as *mut LeanObject,
        ],
    };
pub static l_Lake_Module_precompileImportsFacet___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__0_value)
                as *mut LeanObject,
            9286526061556025856 as *mut LeanObject,
        ],
    };
static mut l_Lake_Module_precompileImportsFacet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Module_precompileImportsFacet: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_precompileImportsFacet___closed__1_value) as *mut LeanObject;
pub static l_Lake_Module_dynlibFacet___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Module_dynlibFacet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__0_value) as *mut LeanObject;
static l_Lake_Module_dynlibFacet___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindModule___closed__0_value) as *mut LeanObject,
        5134674735115079031 as *mut LeanObject,
    ],
};
pub static l_Lake_Module_dynlibFacet___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__0_value) as *mut LeanObject,
        18425581243965226140 as *mut LeanObject,
    ],
};
static mut l_Lake_Module_dynlibFacet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Module_dynlibFacet: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFacet___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanLib_modulesFacet___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LeanLib_modulesFacet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__0_value) as *mut LeanObject;
static l_Lake_LeanLib_modulesFacet___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindLeanLib___closed__0_value) as *mut LeanObject,
        12295998048739818339 as *mut LeanObject,
    ],
};
pub static l_Lake_LeanLib_modulesFacet___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__0_value) as *mut LeanObject,
        15633005100005579590 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanLib_modulesFacet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_LeanLib_modulesFacet: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_modulesFacet___closed__1_value) as *mut LeanObject;
pub static l_Lake_Package_depsFacet___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Package_depsFacet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__0_value) as *mut LeanObject;
static l_Lake_Package_depsFacet___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value) as *mut LeanObject,
        6671755061125946191 as *mut LeanObject,
    ],
};
pub static l_Lake_Package_depsFacet___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__0_value) as *mut LeanObject,
        8196140624318363255 as *mut LeanObject,
    ],
};
static mut l_Lake_Package_depsFacet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Package_depsFacet: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_depsFacet___closed__1_value) as *mut LeanObject;
pub static l_Lake_Package_transDepsFacet___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Package_transDepsFacet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__0_value) as *mut LeanObject;
static l_Lake_Package_transDepsFacet___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instDataKindPackage___closed__0_value) as *mut LeanObject,
        6671755061125946191 as *mut LeanObject,
    ],
};
pub static l_Lake_Package_transDepsFacet___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__0_value) as *mut LeanObject,
        15594444263647844606 as *mut LeanObject,
    ],
};
static mut l_Lake_Package_transDepsFacet___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_Package_transDepsFacet: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Package_transDepsFacet___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lake_Module_key(mut v_self_637_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_643_: u8 = 0;
    let mut v_keyName_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut v_unused_649_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_638_ = lean_ctor_get(v_self_637_, 0);
                v_pkg_639_ = lean_ctor_get(v_lib_638_, 0);
                lean_inc_ref(v_pkg_639_);
                v_name_640_ = lean_ctor_get(v_self_637_, 1);
                v_isSharedCheck_648_ = (!lean_is_exclusive(v_self_637_)) as u8;
                if v_isSharedCheck_648_ == 0 {
                    v_unused_649_ = lean_ctor_get(v_self_637_, 0);
                    lean_dec(v_unused_649_);
                    v___x_642_ = v_self_637_;
                    v_isShared_643_ = v_isSharedCheck_648_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_640_);
                    lean_dec(v_self_637_);
                    v___x_642_ = lean_box(0);
                    v_isShared_643_ = v_isSharedCheck_648_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_keyName_644_ = lean_ctor_get(v_pkg_639_, 2);
                lean_inc(v_keyName_644_);
                lean_dec_ref(v_pkg_639_);
                if v_isShared_643_ == 0 {
                    lean_ctor_set_tag(v___x_642_, 2);
                    lean_ctor_set(v___x_642_, 0, v_keyName_644_);
                    v___x_646_ = v___x_642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_647_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_647_, 0, v_keyName_644_);
                    lean_ctor_set(v_reuseFailAlloc_647_, 1, v_name_640_);
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
    mut v_self_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_651_ = lean_ctor_get(v_self_650_, 0);
    v_name_652_ = lean_ctor_get(v_self_650_, 1);
    v_keyName_653_ = lean_ctor_get(v_pkg_651_, 2);
    lean_inc(v_name_652_);
    lean_inc(v_keyName_653_);
    v___x_654_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_654_, 0, v_keyName_653_);
    lean_ctor_set(v___x_654_, 1, v_name_652_);
    return v___x_654_;
}
pub unsafe fn l_Lake_ConfigTarget_key___redArg___boxed(
    mut v_self_655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_656_: *mut LeanObject = core::ptr::null_mut();
    v_res_656_ = l_Lake_ConfigTarget_key___redArg(v_self_655_);
    lean_dec_ref(v_self_655_);
    return v_res_656_;
}
pub unsafe fn l_Lake_ConfigTarget_key(
    mut v_kind_657_: *mut LeanObject,
    mut v_self_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_659_ = lean_ctor_get(v_self_658_, 0);
    v_name_660_ = lean_ctor_get(v_self_658_, 1);
    v_keyName_661_ = lean_ctor_get(v_pkg_659_, 2);
    lean_inc(v_name_660_);
    lean_inc(v_keyName_661_);
    v___x_662_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_662_, 0, v_keyName_661_);
    lean_ctor_set(v___x_662_, 1, v_name_660_);
    return v___x_662_;
}
pub unsafe fn l_Lake_ConfigTarget_key___boxed(
    mut v_kind_663_: *mut LeanObject,
    mut v_self_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_665_: *mut LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Lake_ConfigTarget_key(v_kind_663_, v_self_664_);
    lean_dec_ref(v_self_664_);
    lean_dec(v_kind_663_);
    return v_res_665_;
}
pub unsafe fn l_Lake_LeanExe_exeBuildKey(mut v_self_666_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_667_ = lean_ctor_get(v_self_666_, 0);
    v_name_668_ = lean_ctor_get(v_self_666_, 1);
    v_keyName_669_ = lean_ctor_get(v_pkg_667_, 2);
    lean_inc(v_name_668_);
    lean_inc(v_keyName_669_);
    v___x_670_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_670_, 0, v_keyName_669_);
    lean_ctor_set(v___x_670_, 1, v_name_668_);
    v___x_671_ = l_Lake_LeanExe_exeFacet;
    v___x_672_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_672_, 0, v___x_670_);
    lean_ctor_set(v___x_672_, 1, v___x_671_);
    return v___x_672_;
}
pub unsafe fn l_Lake_LeanExe_exeBuildKey___boxed(
    mut v_self_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_674_: *mut LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Lake_LeanExe_exeBuildKey(v_self_673_);
    lean_dec_ref(v_self_673_);
    return v_res_674_;
}
pub unsafe fn l_Lake_ExternLib_staticBuildKey(mut v_self_675_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_676_ = lean_ctor_get(v_self_675_, 0);
    v_name_677_ = lean_ctor_get(v_self_675_, 1);
    v_keyName_678_ = lean_ctor_get(v_pkg_676_, 2);
    lean_inc(v_name_677_);
    lean_inc(v_keyName_678_);
    v___x_679_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_679_, 0, v_keyName_678_);
    lean_ctor_set(v___x_679_, 1, v_name_677_);
    v___x_680_ = l_Lake_ExternLib_staticFacet;
    v___x_681_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_681_, 0, v___x_679_);
    lean_ctor_set(v___x_681_, 1, v___x_680_);
    return v___x_681_;
}
pub unsafe fn l_Lake_ExternLib_staticBuildKey___boxed(
    mut v_self_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_683_: *mut LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Lake_ExternLib_staticBuildKey(v_self_682_);
    lean_dec_ref(v_self_682_);
    return v_res_683_;
}
pub unsafe fn l_Lake_ExternLib_sharedBuildKey(mut v_self_684_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_685_ = lean_ctor_get(v_self_684_, 0);
    v_name_686_ = lean_ctor_get(v_self_684_, 1);
    v_keyName_687_ = lean_ctor_get(v_pkg_685_, 2);
    lean_inc(v_name_686_);
    lean_inc(v_keyName_687_);
    v___x_688_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_688_, 0, v_keyName_687_);
    lean_ctor_set(v___x_688_, 1, v_name_686_);
    v___x_689_ = l_Lake_ExternLib_sharedFacet;
    v___x_690_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_690_, 0, v___x_688_);
    lean_ctor_set(v___x_690_, 1, v___x_689_);
    return v___x_690_;
}
pub unsafe fn l_Lake_ExternLib_sharedBuildKey___boxed(
    mut v_self_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_692_: *mut LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Lake_ExternLib_sharedBuildKey(v_self_691_);
    lean_dec_ref(v_self_691_);
    return v_res_692_;
}
pub unsafe fn l_Lake_ExternLib_dynlibBuildKey(mut v_self_693_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_694_ = lean_ctor_get(v_self_693_, 0);
    v_name_695_ = lean_ctor_get(v_self_693_, 1);
    v_keyName_696_ = lean_ctor_get(v_pkg_694_, 2);
    lean_inc(v_name_695_);
    lean_inc(v_keyName_696_);
    v___x_697_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_697_, 0, v_keyName_696_);
    lean_ctor_set(v___x_697_, 1, v_name_695_);
    v___x_698_ = l_Lake_ExternLib_dynlibFacet;
    v___x_699_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_699_, 0, v___x_697_);
    lean_ctor_set(v___x_699_, 1, v___x_698_);
    return v___x_699_;
}
pub unsafe fn l_Lake_ExternLib_dynlibBuildKey___boxed(
    mut v_self_700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_701_: *mut LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lake_ExternLib_dynlibBuildKey(v_self_700_);
    lean_dec_ref(v_self_700_);
    return v_res_701_;
}
pub unsafe fn l_Lake_Module_facetCore(
    mut v_facet_770_: *mut LeanObject,
    mut v_self_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lib_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    v_lib_772_ = lean_ctor_get(v_self_771_, 0);
    v_pkg_773_ = lean_ctor_get(v_lib_772_, 0);
    v_name_774_ = lean_ctor_get(v_self_771_, 1);
    v_keyName_775_ = lean_ctor_get(v_pkg_773_, 2);
    lean_inc(v_name_774_);
    lean_inc(v_keyName_775_);
    v___x_776_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_776_, 0, v_keyName_775_);
    lean_ctor_set(v___x_776_, 1, v_name_774_);
    v___x_777_ = l_Lake_Module_keyword;
    v___x_778_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_778_, 0, v___x_776_);
    lean_ctor_set(v___x_778_, 1, v___x_777_);
    lean_ctor_set(v___x_778_, 2, v_self_771_);
    lean_ctor_set(v___x_778_, 3, v_facet_770_);
    return v___x_778_;
}
pub unsafe fn l_Lake_Module_facet(
    mut v_facet_779_: *mut LeanObject,
    mut v_self_780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lib_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v_lib_781_ = lean_ctor_get(v_self_780_, 0);
    v_pkg_782_ = lean_ctor_get(v_lib_781_, 0);
    v_name_783_ = lean_ctor_get(v_self_780_, 1);
    v_keyName_784_ = lean_ctor_get(v_pkg_782_, 2);
    v___x_785_ = l_Lake_Module_keyword;
    v___x_786_ = l_Lean_Name_append(v___x_785_, v_facet_779_);
    lean_inc(v_name_783_);
    lean_inc(v_keyName_784_);
    v___x_787_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_787_, 0, v_keyName_784_);
    lean_ctor_set(v___x_787_, 1, v_name_783_);
    v___x_788_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_788_, 0, v___x_787_);
    lean_ctor_set(v___x_788_, 1, v___x_785_);
    lean_ctor_set(v___x_788_, 2, v_self_780_);
    lean_ctor_set(v___x_788_, 3, v___x_786_);
    return v___x_788_;
}
pub unsafe fn l_Lake_Module_input(mut v_self_789_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v_lib_790_ = lean_ctor_get(v_self_789_, 0);
    v_pkg_791_ = lean_ctor_get(v_lib_790_, 0);
    v_name_792_ = lean_ctor_get(v_self_789_, 1);
    v_keyName_793_ = lean_ctor_get(v_pkg_791_, 2);
    v___x_794_ = l_Lake_Module_inputFacet;
    lean_inc(v_name_792_);
    lean_inc(v_keyName_793_);
    v___x_795_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_795_, 0, v_keyName_793_);
    lean_ctor_set(v___x_795_, 1, v_name_792_);
    v___x_796_ = l_Lake_Module_keyword;
    v___x_797_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_797_, 0, v___x_795_);
    lean_ctor_set(v___x_797_, 1, v___x_796_);
    lean_ctor_set(v___x_797_, 2, v_self_789_);
    lean_ctor_set(v___x_797_, 3, v___x_794_);
    return v___x_797_;
}
pub unsafe fn l_Lake_Module_lean(mut v_self_798_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    v_lib_799_ = lean_ctor_get(v_self_798_, 0);
    v_pkg_800_ = lean_ctor_get(v_lib_799_, 0);
    v_name_801_ = lean_ctor_get(v_self_798_, 1);
    v_keyName_802_ = lean_ctor_get(v_pkg_800_, 2);
    v___x_803_ = l_Lake_Module_leanFacet;
    lean_inc(v_name_801_);
    lean_inc(v_keyName_802_);
    v___x_804_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_804_, 0, v_keyName_802_);
    lean_ctor_set(v___x_804_, 1, v_name_801_);
    v___x_805_ = l_Lake_Module_keyword;
    v___x_806_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_806_, 0, v___x_804_);
    lean_ctor_set(v___x_806_, 1, v___x_805_);
    lean_ctor_set(v___x_806_, 2, v_self_798_);
    lean_ctor_set(v___x_806_, 3, v___x_803_);
    return v___x_806_;
}
pub unsafe fn l_Lake_Module_header(mut v_self_807_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    v_lib_808_ = lean_ctor_get(v_self_807_, 0);
    v_pkg_809_ = lean_ctor_get(v_lib_808_, 0);
    v_name_810_ = lean_ctor_get(v_self_807_, 1);
    v_keyName_811_ = lean_ctor_get(v_pkg_809_, 2);
    v___x_812_ = l_Lake_Module_headerFacet;
    lean_inc(v_name_810_);
    lean_inc(v_keyName_811_);
    v___x_813_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_813_, 0, v_keyName_811_);
    lean_ctor_set(v___x_813_, 1, v_name_810_);
    v___x_814_ = l_Lake_Module_keyword;
    v___x_815_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_815_, 0, v___x_813_);
    lean_ctor_set(v___x_815_, 1, v___x_814_);
    lean_ctor_set(v___x_815_, 2, v_self_807_);
    lean_ctor_set(v___x_815_, 3, v___x_812_);
    return v___x_815_;
}
pub unsafe fn l_Lake_Module_imports(mut v_self_816_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    v_lib_817_ = lean_ctor_get(v_self_816_, 0);
    v_pkg_818_ = lean_ctor_get(v_lib_817_, 0);
    v_name_819_ = lean_ctor_get(v_self_816_, 1);
    v_keyName_820_ = lean_ctor_get(v_pkg_818_, 2);
    v___x_821_ = l_Lake_Module_importsFacet;
    lean_inc(v_name_819_);
    lean_inc(v_keyName_820_);
    v___x_822_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_822_, 0, v_keyName_820_);
    lean_ctor_set(v___x_822_, 1, v_name_819_);
    v___x_823_ = l_Lake_Module_keyword;
    v___x_824_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_824_, 0, v___x_822_);
    lean_ctor_set(v___x_824_, 1, v___x_823_);
    lean_ctor_set(v___x_824_, 2, v_self_816_);
    lean_ctor_set(v___x_824_, 3, v___x_821_);
    return v___x_824_;
}
pub unsafe fn l_Lake_Module_transImports(mut v_self_825_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    v_lib_826_ = lean_ctor_get(v_self_825_, 0);
    v_pkg_827_ = lean_ctor_get(v_lib_826_, 0);
    v_name_828_ = lean_ctor_get(v_self_825_, 1);
    v_keyName_829_ = lean_ctor_get(v_pkg_827_, 2);
    v___x_830_ = l_Lake_Module_transImportsFacet;
    lean_inc(v_name_828_);
    lean_inc(v_keyName_829_);
    v___x_831_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_831_, 0, v_keyName_829_);
    lean_ctor_set(v___x_831_, 1, v_name_828_);
    v___x_832_ = l_Lake_Module_keyword;
    v___x_833_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_833_, 0, v___x_831_);
    lean_ctor_set(v___x_833_, 1, v___x_832_);
    lean_ctor_set(v___x_833_, 2, v_self_825_);
    lean_ctor_set(v___x_833_, 3, v___x_830_);
    return v___x_833_;
}
pub unsafe fn l_Lake_Module_precompileImports(mut v_self_834_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    v_lib_835_ = lean_ctor_get(v_self_834_, 0);
    v_pkg_836_ = lean_ctor_get(v_lib_835_, 0);
    v_name_837_ = lean_ctor_get(v_self_834_, 1);
    v_keyName_838_ = lean_ctor_get(v_pkg_836_, 2);
    v___x_839_ = l_Lake_Module_precompileImportsFacet;
    lean_inc(v_name_837_);
    lean_inc(v_keyName_838_);
    v___x_840_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_840_, 0, v_keyName_838_);
    lean_ctor_set(v___x_840_, 1, v_name_837_);
    v___x_841_ = l_Lake_Module_keyword;
    v___x_842_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_842_, 0, v___x_840_);
    lean_ctor_set(v___x_842_, 1, v___x_841_);
    lean_ctor_set(v___x_842_, 2, v_self_834_);
    lean_ctor_set(v___x_842_, 3, v___x_839_);
    return v___x_842_;
}
pub unsafe fn l_Lake_Module_setup(mut v_self_843_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    v_lib_844_ = lean_ctor_get(v_self_843_, 0);
    v_pkg_845_ = lean_ctor_get(v_lib_844_, 0);
    v_name_846_ = lean_ctor_get(v_self_843_, 1);
    v_keyName_847_ = lean_ctor_get(v_pkg_845_, 2);
    v___x_848_ = l_Lake_Module_setupFacet;
    lean_inc(v_name_846_);
    lean_inc(v_keyName_847_);
    v___x_849_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_849_, 0, v_keyName_847_);
    lean_ctor_set(v___x_849_, 1, v_name_846_);
    v___x_850_ = l_Lake_Module_keyword;
    v___x_851_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_851_, 0, v___x_849_);
    lean_ctor_set(v___x_851_, 1, v___x_850_);
    lean_ctor_set(v___x_851_, 2, v_self_843_);
    lean_ctor_set(v___x_851_, 3, v___x_848_);
    return v___x_851_;
}
pub unsafe fn l_Lake_Module_deps(mut v_self_852_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    v_lib_853_ = lean_ctor_get(v_self_852_, 0);
    v_pkg_854_ = lean_ctor_get(v_lib_853_, 0);
    v_name_855_ = lean_ctor_get(v_self_852_, 1);
    v_keyName_856_ = lean_ctor_get(v_pkg_854_, 2);
    v___x_857_ = l_Lake_Module_depsFacet;
    lean_inc(v_name_855_);
    lean_inc(v_keyName_856_);
    v___x_858_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_858_, 0, v_keyName_856_);
    lean_ctor_set(v___x_858_, 1, v_name_855_);
    v___x_859_ = l_Lake_Module_keyword;
    v___x_860_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_860_, 0, v___x_858_);
    lean_ctor_set(v___x_860_, 1, v___x_859_);
    lean_ctor_set(v___x_860_, 2, v_self_852_);
    lean_ctor_set(v___x_860_, 3, v___x_857_);
    return v___x_860_;
}
pub unsafe fn l_Lake_Module_importInfo(mut v_self_861_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    v_lib_862_ = lean_ctor_get(v_self_861_, 0);
    v_pkg_863_ = lean_ctor_get(v_lib_862_, 0);
    v_name_864_ = lean_ctor_get(v_self_861_, 1);
    v_keyName_865_ = lean_ctor_get(v_pkg_863_, 2);
    v___x_866_ = l_Lake_Module_importInfoFacet;
    lean_inc(v_name_864_);
    lean_inc(v_keyName_865_);
    v___x_867_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_867_, 0, v_keyName_865_);
    lean_ctor_set(v___x_867_, 1, v_name_864_);
    v___x_868_ = l_Lake_Module_keyword;
    v___x_869_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_869_, 0, v___x_867_);
    lean_ctor_set(v___x_869_, 1, v___x_868_);
    lean_ctor_set(v___x_869_, 2, v_self_861_);
    lean_ctor_set(v___x_869_, 3, v___x_866_);
    return v___x_869_;
}
pub unsafe fn l_Lake_Module_exportInfo(mut v_self_870_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    v_lib_871_ = lean_ctor_get(v_self_870_, 0);
    v_pkg_872_ = lean_ctor_get(v_lib_871_, 0);
    v_name_873_ = lean_ctor_get(v_self_870_, 1);
    v_keyName_874_ = lean_ctor_get(v_pkg_872_, 2);
    v___x_875_ = l_Lake_Module_exportInfoFacet;
    lean_inc(v_name_873_);
    lean_inc(v_keyName_874_);
    v___x_876_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_876_, 0, v_keyName_874_);
    lean_ctor_set(v___x_876_, 1, v_name_873_);
    v___x_877_ = l_Lake_Module_keyword;
    v___x_878_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_878_, 0, v___x_876_);
    lean_ctor_set(v___x_878_, 1, v___x_877_);
    lean_ctor_set(v___x_878_, 2, v_self_870_);
    lean_ctor_set(v___x_878_, 3, v___x_875_);
    return v___x_878_;
}
pub unsafe fn l_Lake_Module_importArts(mut v_self_879_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    v_lib_880_ = lean_ctor_get(v_self_879_, 0);
    v_pkg_881_ = lean_ctor_get(v_lib_880_, 0);
    v_name_882_ = lean_ctor_get(v_self_879_, 1);
    v_keyName_883_ = lean_ctor_get(v_pkg_881_, 2);
    v___x_884_ = l_Lake_Module_importArtsFacet;
    lean_inc(v_name_882_);
    lean_inc(v_keyName_883_);
    v___x_885_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_885_, 0, v_keyName_883_);
    lean_ctor_set(v___x_885_, 1, v_name_882_);
    v___x_886_ = l_Lake_Module_keyword;
    v___x_887_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_887_, 0, v___x_885_);
    lean_ctor_set(v___x_887_, 1, v___x_886_);
    lean_ctor_set(v___x_887_, 2, v_self_879_);
    lean_ctor_set(v___x_887_, 3, v___x_884_);
    return v___x_887_;
}
pub unsafe fn l_Lake_Module_importAllArts(mut v_self_888_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    v_lib_889_ = lean_ctor_get(v_self_888_, 0);
    v_pkg_890_ = lean_ctor_get(v_lib_889_, 0);
    v_name_891_ = lean_ctor_get(v_self_888_, 1);
    v_keyName_892_ = lean_ctor_get(v_pkg_890_, 2);
    v___x_893_ = l_Lake_Module_importAllArtsFacet;
    lean_inc(v_name_891_);
    lean_inc(v_keyName_892_);
    v___x_894_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_894_, 0, v_keyName_892_);
    lean_ctor_set(v___x_894_, 1, v_name_891_);
    v___x_895_ = l_Lake_Module_keyword;
    v___x_896_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_896_, 0, v___x_894_);
    lean_ctor_set(v___x_896_, 1, v___x_895_);
    lean_ctor_set(v___x_896_, 2, v_self_888_);
    lean_ctor_set(v___x_896_, 3, v___x_893_);
    return v___x_896_;
}
pub unsafe fn l_Lake_Module_leanArts(mut v_self_897_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    v_lib_898_ = lean_ctor_get(v_self_897_, 0);
    v_pkg_899_ = lean_ctor_get(v_lib_898_, 0);
    v_name_900_ = lean_ctor_get(v_self_897_, 1);
    v_keyName_901_ = lean_ctor_get(v_pkg_899_, 2);
    v___x_902_ = l_Lake_Module_leanArtsFacet;
    lean_inc(v_name_900_);
    lean_inc(v_keyName_901_);
    v___x_903_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_903_, 0, v_keyName_901_);
    lean_ctor_set(v___x_903_, 1, v_name_900_);
    v___x_904_ = l_Lake_Module_keyword;
    v___x_905_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_905_, 0, v___x_903_);
    lean_ctor_set(v___x_905_, 1, v___x_904_);
    lean_ctor_set(v___x_905_, 2, v_self_897_);
    lean_ctor_set(v___x_905_, 3, v___x_902_);
    return v___x_905_;
}
pub unsafe fn l_Lake_Module_olean(mut v_self_906_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v_lib_907_ = lean_ctor_get(v_self_906_, 0);
    v_pkg_908_ = lean_ctor_get(v_lib_907_, 0);
    v_name_909_ = lean_ctor_get(v_self_906_, 1);
    v_keyName_910_ = lean_ctor_get(v_pkg_908_, 2);
    v___x_911_ = l_Lake_Module_oleanFacet;
    lean_inc(v_name_909_);
    lean_inc(v_keyName_910_);
    v___x_912_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_912_, 0, v_keyName_910_);
    lean_ctor_set(v___x_912_, 1, v_name_909_);
    v___x_913_ = l_Lake_Module_keyword;
    v___x_914_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_914_, 0, v___x_912_);
    lean_ctor_set(v___x_914_, 1, v___x_913_);
    lean_ctor_set(v___x_914_, 2, v_self_906_);
    lean_ctor_set(v___x_914_, 3, v___x_911_);
    return v___x_914_;
}
pub unsafe fn l_Lake_Module_oleanServer(mut v_self_915_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    v_lib_916_ = lean_ctor_get(v_self_915_, 0);
    v_pkg_917_ = lean_ctor_get(v_lib_916_, 0);
    v_name_918_ = lean_ctor_get(v_self_915_, 1);
    v_keyName_919_ = lean_ctor_get(v_pkg_917_, 2);
    v___x_920_ = l_Lake_Module_oleanServerFacet;
    lean_inc(v_name_918_);
    lean_inc(v_keyName_919_);
    v___x_921_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_921_, 0, v_keyName_919_);
    lean_ctor_set(v___x_921_, 1, v_name_918_);
    v___x_922_ = l_Lake_Module_keyword;
    v___x_923_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_923_, 0, v___x_921_);
    lean_ctor_set(v___x_923_, 1, v___x_922_);
    lean_ctor_set(v___x_923_, 2, v_self_915_);
    lean_ctor_set(v___x_923_, 3, v___x_920_);
    return v___x_923_;
}
pub unsafe fn l_Lake_Module_oleanPrivate(mut v_self_924_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    v_lib_925_ = lean_ctor_get(v_self_924_, 0);
    v_pkg_926_ = lean_ctor_get(v_lib_925_, 0);
    v_name_927_ = lean_ctor_get(v_self_924_, 1);
    v_keyName_928_ = lean_ctor_get(v_pkg_926_, 2);
    v___x_929_ = l_Lake_Module_oleanPrivateFacet;
    lean_inc(v_name_927_);
    lean_inc(v_keyName_928_);
    v___x_930_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_930_, 0, v_keyName_928_);
    lean_ctor_set(v___x_930_, 1, v_name_927_);
    v___x_931_ = l_Lake_Module_keyword;
    v___x_932_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_932_, 0, v___x_930_);
    lean_ctor_set(v___x_932_, 1, v___x_931_);
    lean_ctor_set(v___x_932_, 2, v_self_924_);
    lean_ctor_set(v___x_932_, 3, v___x_929_);
    return v___x_932_;
}
pub unsafe fn l_Lake_Module_ilean(mut v_self_933_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    v_lib_934_ = lean_ctor_get(v_self_933_, 0);
    v_pkg_935_ = lean_ctor_get(v_lib_934_, 0);
    v_name_936_ = lean_ctor_get(v_self_933_, 1);
    v_keyName_937_ = lean_ctor_get(v_pkg_935_, 2);
    v___x_938_ = l_Lake_Module_ileanFacet;
    lean_inc(v_name_936_);
    lean_inc(v_keyName_937_);
    v___x_939_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_939_, 0, v_keyName_937_);
    lean_ctor_set(v___x_939_, 1, v_name_936_);
    v___x_940_ = l_Lake_Module_keyword;
    v___x_941_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_941_, 0, v___x_939_);
    lean_ctor_set(v___x_941_, 1, v___x_940_);
    lean_ctor_set(v___x_941_, 2, v_self_933_);
    lean_ctor_set(v___x_941_, 3, v___x_938_);
    return v___x_941_;
}
pub unsafe fn l_Lake_Module_ir(mut v_self_942_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v_lib_943_ = lean_ctor_get(v_self_942_, 0);
    v_pkg_944_ = lean_ctor_get(v_lib_943_, 0);
    v_name_945_ = lean_ctor_get(v_self_942_, 1);
    v_keyName_946_ = lean_ctor_get(v_pkg_944_, 2);
    v___x_947_ = l_Lake_Module_irFacet;
    lean_inc(v_name_945_);
    lean_inc(v_keyName_946_);
    v___x_948_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_948_, 0, v_keyName_946_);
    lean_ctor_set(v___x_948_, 1, v_name_945_);
    v___x_949_ = l_Lake_Module_keyword;
    v___x_950_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_950_, 0, v___x_948_);
    lean_ctor_set(v___x_950_, 1, v___x_949_);
    lean_ctor_set(v___x_950_, 2, v_self_942_);
    lean_ctor_set(v___x_950_, 3, v___x_947_);
    return v___x_950_;
}
pub unsafe fn l_Lake_Module_c(mut v_self_951_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    v_lib_952_ = lean_ctor_get(v_self_951_, 0);
    v_pkg_953_ = lean_ctor_get(v_lib_952_, 0);
    v_name_954_ = lean_ctor_get(v_self_951_, 1);
    v_keyName_955_ = lean_ctor_get(v_pkg_953_, 2);
    v___x_956_ = l_Lake_Module_cFacet;
    lean_inc(v_name_954_);
    lean_inc(v_keyName_955_);
    v___x_957_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_957_, 0, v_keyName_955_);
    lean_ctor_set(v___x_957_, 1, v_name_954_);
    v___x_958_ = l_Lake_Module_keyword;
    v___x_959_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_959_, 0, v___x_957_);
    lean_ctor_set(v___x_959_, 1, v___x_958_);
    lean_ctor_set(v___x_959_, 2, v_self_951_);
    lean_ctor_set(v___x_959_, 3, v___x_956_);
    return v___x_959_;
}
pub unsafe fn l_Lake_Module_bc(mut v_self_960_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    v_lib_961_ = lean_ctor_get(v_self_960_, 0);
    v_pkg_962_ = lean_ctor_get(v_lib_961_, 0);
    v_name_963_ = lean_ctor_get(v_self_960_, 1);
    v_keyName_964_ = lean_ctor_get(v_pkg_962_, 2);
    v___x_965_ = l_Lake_Module_bcFacet;
    lean_inc(v_name_963_);
    lean_inc(v_keyName_964_);
    v___x_966_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_966_, 0, v_keyName_964_);
    lean_ctor_set(v___x_966_, 1, v_name_963_);
    v___x_967_ = l_Lake_Module_keyword;
    v___x_968_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_968_, 0, v___x_966_);
    lean_ctor_set(v___x_968_, 1, v___x_967_);
    lean_ctor_set(v___x_968_, 2, v_self_960_);
    lean_ctor_set(v___x_968_, 3, v___x_965_);
    return v___x_968_;
}
pub unsafe fn l_Lake_Module_ltar(mut v_self_969_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    v_lib_970_ = lean_ctor_get(v_self_969_, 0);
    v_pkg_971_ = lean_ctor_get(v_lib_970_, 0);
    v_name_972_ = lean_ctor_get(v_self_969_, 1);
    v_keyName_973_ = lean_ctor_get(v_pkg_971_, 2);
    v___x_974_ = l_Lake_Module_ltarFacet;
    lean_inc(v_name_972_);
    lean_inc(v_keyName_973_);
    v___x_975_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_975_, 0, v_keyName_973_);
    lean_ctor_set(v___x_975_, 1, v_name_972_);
    v___x_976_ = l_Lake_Module_keyword;
    v___x_977_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_977_, 0, v___x_975_);
    lean_ctor_set(v___x_977_, 1, v___x_976_);
    lean_ctor_set(v___x_977_, 2, v_self_969_);
    lean_ctor_set(v___x_977_, 3, v___x_974_);
    return v___x_977_;
}
pub unsafe fn l_Lake_Module_o(mut v_self_978_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    v_lib_979_ = lean_ctor_get(v_self_978_, 0);
    v_pkg_980_ = lean_ctor_get(v_lib_979_, 0);
    v_name_981_ = lean_ctor_get(v_self_978_, 1);
    v_keyName_982_ = lean_ctor_get(v_pkg_980_, 2);
    v___x_983_ = l_Lake_Module_oFacet;
    lean_inc(v_name_981_);
    lean_inc(v_keyName_982_);
    v___x_984_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_984_, 0, v_keyName_982_);
    lean_ctor_set(v___x_984_, 1, v_name_981_);
    v___x_985_ = l_Lake_Module_keyword;
    v___x_986_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_986_, 0, v___x_984_);
    lean_ctor_set(v___x_986_, 1, v___x_985_);
    lean_ctor_set(v___x_986_, 2, v_self_978_);
    lean_ctor_set(v___x_986_, 3, v___x_983_);
    return v___x_986_;
}
pub unsafe fn l_Lake_Module_oExport(mut v_self_987_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    v_lib_988_ = lean_ctor_get(v_self_987_, 0);
    v_pkg_989_ = lean_ctor_get(v_lib_988_, 0);
    v_name_990_ = lean_ctor_get(v_self_987_, 1);
    v_keyName_991_ = lean_ctor_get(v_pkg_989_, 2);
    v___x_992_ = l_Lake_Module_oExportFacet;
    lean_inc(v_name_990_);
    lean_inc(v_keyName_991_);
    v___x_993_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_993_, 0, v_keyName_991_);
    lean_ctor_set(v___x_993_, 1, v_name_990_);
    v___x_994_ = l_Lake_Module_keyword;
    v___x_995_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_995_, 0, v___x_993_);
    lean_ctor_set(v___x_995_, 1, v___x_994_);
    lean_ctor_set(v___x_995_, 2, v_self_987_);
    lean_ctor_set(v___x_995_, 3, v___x_992_);
    return v___x_995_;
}
pub unsafe fn l_Lake_Module_oNoExport(mut v_self_996_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    v_lib_997_ = lean_ctor_get(v_self_996_, 0);
    v_pkg_998_ = lean_ctor_get(v_lib_997_, 0);
    v_name_999_ = lean_ctor_get(v_self_996_, 1);
    v_keyName_1000_ = lean_ctor_get(v_pkg_998_, 2);
    v___x_1001_ = l_Lake_Module_oNoExportFacet;
    lean_inc(v_name_999_);
    lean_inc(v_keyName_1000_);
    v___x_1002_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_1002_, 0, v_keyName_1000_);
    lean_ctor_set(v___x_1002_, 1, v_name_999_);
    v___x_1003_ = l_Lake_Module_keyword;
    v___x_1004_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1004_, 0, v___x_1002_);
    lean_ctor_set(v___x_1004_, 1, v___x_1003_);
    lean_ctor_set(v___x_1004_, 2, v_self_996_);
    lean_ctor_set(v___x_1004_, 3, v___x_1001_);
    return v___x_1004_;
}
pub unsafe fn l_Lake_Module_co(mut v_self_1005_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    v_lib_1006_ = lean_ctor_get(v_self_1005_, 0);
    v_pkg_1007_ = lean_ctor_get(v_lib_1006_, 0);
    v_name_1008_ = lean_ctor_get(v_self_1005_, 1);
    v_keyName_1009_ = lean_ctor_get(v_pkg_1007_, 2);
    v___x_1010_ = l_Lake_Module_coFacet;
    lean_inc(v_name_1008_);
    lean_inc(v_keyName_1009_);
    v___x_1011_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_1011_, 0, v_keyName_1009_);
    lean_ctor_set(v___x_1011_, 1, v_name_1008_);
    v___x_1012_ = l_Lake_Module_keyword;
    v___x_1013_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1013_, 0, v___x_1011_);
    lean_ctor_set(v___x_1013_, 1, v___x_1012_);
    lean_ctor_set(v___x_1013_, 2, v_self_1005_);
    lean_ctor_set(v___x_1013_, 3, v___x_1010_);
    return v___x_1013_;
}
pub unsafe fn l_Lake_Module_coExport(mut v_self_1014_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    v_lib_1015_ = lean_ctor_get(v_self_1014_, 0);
    v_pkg_1016_ = lean_ctor_get(v_lib_1015_, 0);
    v_name_1017_ = lean_ctor_get(v_self_1014_, 1);
    v_keyName_1018_ = lean_ctor_get(v_pkg_1016_, 2);
    v___x_1019_ = l_Lake_Module_coExportFacet;
    lean_inc(v_name_1017_);
    lean_inc(v_keyName_1018_);
    v___x_1020_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_1020_, 0, v_keyName_1018_);
    lean_ctor_set(v___x_1020_, 1, v_name_1017_);
    v___x_1021_ = l_Lake_Module_keyword;
    v___x_1022_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1022_, 0, v___x_1020_);
    lean_ctor_set(v___x_1022_, 1, v___x_1021_);
    lean_ctor_set(v___x_1022_, 2, v_self_1014_);
    lean_ctor_set(v___x_1022_, 3, v___x_1019_);
    return v___x_1022_;
}
pub unsafe fn l_Lake_Module_coNoExport(mut v_self_1023_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    v_lib_1024_ = lean_ctor_get(v_self_1023_, 0);
    v_pkg_1025_ = lean_ctor_get(v_lib_1024_, 0);
    v_name_1026_ = lean_ctor_get(v_self_1023_, 1);
    v_keyName_1027_ = lean_ctor_get(v_pkg_1025_, 2);
    v___x_1028_ = l_Lake_Module_coNoExportFacet;
    lean_inc(v_name_1026_);
    lean_inc(v_keyName_1027_);
    v___x_1029_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_1029_, 0, v_keyName_1027_);
    lean_ctor_set(v___x_1029_, 1, v_name_1026_);
    v___x_1030_ = l_Lake_Module_keyword;
    v___x_1031_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1031_, 0, v___x_1029_);
    lean_ctor_set(v___x_1031_, 1, v___x_1030_);
    lean_ctor_set(v___x_1031_, 2, v_self_1023_);
    lean_ctor_set(v___x_1031_, 3, v___x_1028_);
    return v___x_1031_;
}
pub unsafe fn l_Lake_Module_bco(mut v_self_1032_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    v_lib_1033_ = lean_ctor_get(v_self_1032_, 0);
    v_pkg_1034_ = lean_ctor_get(v_lib_1033_, 0);
    v_name_1035_ = lean_ctor_get(v_self_1032_, 1);
    v_keyName_1036_ = lean_ctor_get(v_pkg_1034_, 2);
    v___x_1037_ = l_Lake_Module_bcoFacet;
    lean_inc(v_name_1035_);
    lean_inc(v_keyName_1036_);
    v___x_1038_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_1038_, 0, v_keyName_1036_);
    lean_ctor_set(v___x_1038_, 1, v_name_1035_);
    v___x_1039_ = l_Lake_Module_keyword;
    v___x_1040_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1040_, 0, v___x_1038_);
    lean_ctor_set(v___x_1040_, 1, v___x_1039_);
    lean_ctor_set(v___x_1040_, 2, v_self_1032_);
    lean_ctor_set(v___x_1040_, 3, v___x_1037_);
    return v___x_1040_;
}
pub unsafe fn l_Lake_Module_dynlib(mut v_self_1041_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lib_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    v_lib_1042_ = lean_ctor_get(v_self_1041_, 0);
    v_pkg_1043_ = lean_ctor_get(v_lib_1042_, 0);
    v_name_1044_ = lean_ctor_get(v_self_1041_, 1);
    v_keyName_1045_ = lean_ctor_get(v_pkg_1043_, 2);
    v___x_1046_ = l_Lake_Module_dynlibFacet;
    lean_inc(v_name_1044_);
    lean_inc(v_keyName_1045_);
    v___x_1047_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_1047_, 0, v_keyName_1045_);
    lean_ctor_set(v___x_1047_, 1, v_name_1044_);
    v___x_1048_ = l_Lake_Module_keyword;
    v___x_1049_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1049_, 0, v___x_1047_);
    lean_ctor_set(v___x_1049_, 1, v___x_1048_);
    lean_ctor_set(v___x_1049_, 2, v_self_1041_);
    lean_ctor_set(v___x_1049_, 3, v___x_1046_);
    return v___x_1049_;
}
pub unsafe fn l_Lake_Package_target(
    mut v_target_1050_: *mut LeanObject,
    mut v_self_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1052_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1052_, 0, v_self_1051_);
    lean_ctor_set(v___x_1052_, 1, v_target_1050_);
    return v___x_1052_;
}
pub unsafe fn l_Lake_Package_facetCore(
    mut v_facet_1053_: *mut LeanObject,
    mut v_self_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyName_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1055_ = lean_ctor_get(v_self_1054_, 2);
    lean_inc(v_keyName_1055_);
    v___x_1056_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1056_, 0, v_keyName_1055_);
    v___x_1057_ = l_Lake_Package_keyword;
    v___x_1058_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1058_, 0, v___x_1056_);
    lean_ctor_set(v___x_1058_, 1, v___x_1057_);
    lean_ctor_set(v___x_1058_, 2, v_self_1054_);
    lean_ctor_set(v___x_1058_, 3, v_facet_1053_);
    return v___x_1058_;
}
pub unsafe fn l_Lake_Package_facet(
    mut v_facet_1059_: *mut LeanObject,
    mut v_self_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyName_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1061_ = lean_ctor_get(v_self_1060_, 2);
    v___x_1062_ = l_Lake_Package_keyword;
    v___x_1063_ = l_Lean_Name_append(v___x_1062_, v_facet_1059_);
    lean_inc(v_keyName_1061_);
    v___x_1064_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1064_, 0, v_keyName_1061_);
    v___x_1065_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1065_, 0, v___x_1064_);
    lean_ctor_set(v___x_1065_, 1, v___x_1062_);
    lean_ctor_set(v___x_1065_, 2, v_self_1060_);
    lean_ctor_set(v___x_1065_, 3, v___x_1063_);
    return v___x_1065_;
}
pub unsafe fn l_Lake_Package_buildCache(mut v_self_1066_: *mut LeanObject) -> *mut LeanObject {
    let mut v_keyName_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1067_ = lean_ctor_get(v_self_1066_, 2);
    v___x_1068_ = l_Lake_Package_buildCacheFacet;
    lean_inc(v_keyName_1067_);
    v___x_1069_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1069_, 0, v_keyName_1067_);
    v___x_1070_ = l_Lake_Package_keyword;
    v___x_1071_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1071_, 0, v___x_1069_);
    lean_ctor_set(v___x_1071_, 1, v___x_1070_);
    lean_ctor_set(v___x_1071_, 2, v_self_1066_);
    lean_ctor_set(v___x_1071_, 3, v___x_1068_);
    return v___x_1071_;
}
pub unsafe fn l_Lake_Package_optBuildCache(mut v_self_1072_: *mut LeanObject) -> *mut LeanObject {
    let mut v_keyName_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1073_ = lean_ctor_get(v_self_1072_, 2);
    v___x_1074_ = l_Lake_Package_optBuildCacheFacet;
    lean_inc(v_keyName_1073_);
    v___x_1075_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1075_, 0, v_keyName_1073_);
    v___x_1076_ = l_Lake_Package_keyword;
    v___x_1077_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1077_, 0, v___x_1075_);
    lean_ctor_set(v___x_1077_, 1, v___x_1076_);
    lean_ctor_set(v___x_1077_, 2, v_self_1072_);
    lean_ctor_set(v___x_1077_, 3, v___x_1074_);
    return v___x_1077_;
}
pub unsafe fn l_Lake_Package_reservoirBarrel(mut v_self_1078_: *mut LeanObject) -> *mut LeanObject {
    let mut v_keyName_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1079_ = lean_ctor_get(v_self_1078_, 2);
    v___x_1080_ = l_Lake_Package_reservoirBarrelFacet;
    lean_inc(v_keyName_1079_);
    v___x_1081_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1081_, 0, v_keyName_1079_);
    v___x_1082_ = l_Lake_Package_keyword;
    v___x_1083_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1083_, 0, v___x_1081_);
    lean_ctor_set(v___x_1083_, 1, v___x_1082_);
    lean_ctor_set(v___x_1083_, 2, v_self_1078_);
    lean_ctor_set(v___x_1083_, 3, v___x_1080_);
    return v___x_1083_;
}
pub unsafe fn l_Lake_Package_optReservoirBarrel(
    mut v_self_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyName_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1085_ = lean_ctor_get(v_self_1084_, 2);
    v___x_1086_ = l_Lake_Package_optReservoirBarrelFacet;
    lean_inc(v_keyName_1085_);
    v___x_1087_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1087_, 0, v_keyName_1085_);
    v___x_1088_ = l_Lake_Package_keyword;
    v___x_1089_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1089_, 0, v___x_1087_);
    lean_ctor_set(v___x_1089_, 1, v___x_1088_);
    lean_ctor_set(v___x_1089_, 2, v_self_1084_);
    lean_ctor_set(v___x_1089_, 3, v___x_1086_);
    return v___x_1089_;
}
pub unsafe fn l_Lake_Package_gitHubRelease(mut v_self_1090_: *mut LeanObject) -> *mut LeanObject {
    let mut v_keyName_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1091_ = lean_ctor_get(v_self_1090_, 2);
    v___x_1092_ = l_Lake_Package_gitHubReleaseFacet;
    lean_inc(v_keyName_1091_);
    v___x_1093_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1093_, 0, v_keyName_1091_);
    v___x_1094_ = l_Lake_Package_keyword;
    v___x_1095_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1095_, 0, v___x_1093_);
    lean_ctor_set(v___x_1095_, 1, v___x_1094_);
    lean_ctor_set(v___x_1095_, 2, v_self_1090_);
    lean_ctor_set(v___x_1095_, 3, v___x_1092_);
    return v___x_1095_;
}
pub unsafe fn l_Lake_Package_optGitHubRelease(
    mut v_self_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyName_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1097_ = lean_ctor_get(v_self_1096_, 2);
    v___x_1098_ = l_Lake_Package_optGitHubReleaseFacet;
    lean_inc(v_keyName_1097_);
    v___x_1099_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1099_, 0, v_keyName_1097_);
    v___x_1100_ = l_Lake_Package_keyword;
    v___x_1101_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1101_, 0, v___x_1099_);
    lean_ctor_set(v___x_1101_, 1, v___x_1100_);
    lean_ctor_set(v___x_1101_, 2, v_self_1096_);
    lean_ctor_set(v___x_1101_, 3, v___x_1098_);
    return v___x_1101_;
}
pub unsafe fn l_Lake_Package_extraDep(mut v_self_1102_: *mut LeanObject) -> *mut LeanObject {
    let mut v_keyName_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1103_ = lean_ctor_get(v_self_1102_, 2);
    v___x_1104_ = l_Lake_Package_extraDepFacet;
    lean_inc(v_keyName_1103_);
    v___x_1105_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1105_, 0, v_keyName_1103_);
    v___x_1106_ = l_Lake_Package_keyword;
    v___x_1107_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1107_, 0, v___x_1105_);
    lean_ctor_set(v___x_1107_, 1, v___x_1106_);
    lean_ctor_set(v___x_1107_, 2, v_self_1102_);
    lean_ctor_set(v___x_1107_, 3, v___x_1104_);
    return v___x_1107_;
}
pub unsafe fn l_Lake_Package_deps(mut v_self_1108_: *mut LeanObject) -> *mut LeanObject {
    let mut v_keyName_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1109_ = lean_ctor_get(v_self_1108_, 2);
    v___x_1110_ = l_Lake_Package_depsFacet;
    lean_inc(v_keyName_1109_);
    v___x_1111_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1111_, 0, v_keyName_1109_);
    v___x_1112_ = l_Lake_Package_keyword;
    v___x_1113_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1113_, 0, v___x_1111_);
    lean_ctor_set(v___x_1113_, 1, v___x_1112_);
    lean_ctor_set(v___x_1113_, 2, v_self_1108_);
    lean_ctor_set(v___x_1113_, 3, v___x_1110_);
    return v___x_1113_;
}
pub unsafe fn l_Lake_Package_transDeps(mut v_self_1114_: *mut LeanObject) -> *mut LeanObject {
    let mut v_keyName_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    v_keyName_1115_ = lean_ctor_get(v_self_1114_, 2);
    v___x_1116_ = l_Lake_Package_transDepsFacet;
    lean_inc(v_keyName_1115_);
    v___x_1117_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1117_, 0, v_keyName_1115_);
    v___x_1118_ = l_Lake_Package_keyword;
    v___x_1119_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1119_, 0, v___x_1117_);
    lean_ctor_set(v___x_1119_, 1, v___x_1118_);
    lean_ctor_set(v___x_1119_, 2, v_self_1114_);
    lean_ctor_set(v___x_1119_, 3, v___x_1116_);
    return v___x_1119_;
}
pub unsafe fn l_Lake_LeanLib_facetCore(
    mut v_facet_1120_: *mut LeanObject,
    mut v_self_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1122_ = lean_ctor_get(v_self_1121_, 0);
    v_name_1123_ = lean_ctor_get(v_self_1121_, 1);
    v_keyName_1124_ = lean_ctor_get(v_pkg_1122_, 2);
    lean_inc(v_name_1123_);
    lean_inc(v_keyName_1124_);
    v___x_1125_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1125_, 0, v_keyName_1124_);
    lean_ctor_set(v___x_1125_, 1, v_name_1123_);
    v___x_1126_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1127_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1127_, 0, v___x_1125_);
    lean_ctor_set(v___x_1127_, 1, v___x_1126_);
    lean_ctor_set(v___x_1127_, 2, v_self_1121_);
    lean_ctor_set(v___x_1127_, 3, v_facet_1120_);
    return v___x_1127_;
}
pub unsafe fn l_Lake_LeanLib_facet(
    mut v_facet_1128_: *mut LeanObject,
    mut v_self_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1130_ = lean_ctor_get(v_self_1129_, 0);
    v_name_1131_ = lean_ctor_get(v_self_1129_, 1);
    v_keyName_1132_ = lean_ctor_get(v_pkg_1130_, 2);
    v___x_1133_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1134_ = l_Lean_Name_append(v___x_1133_, v_facet_1128_);
    lean_inc(v_name_1131_);
    lean_inc(v_keyName_1132_);
    v___x_1135_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1135_, 0, v_keyName_1132_);
    lean_ctor_set(v___x_1135_, 1, v_name_1131_);
    v___x_1136_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1136_, 0, v___x_1135_);
    lean_ctor_set(v___x_1136_, 1, v___x_1133_);
    lean_ctor_set(v___x_1136_, 2, v_self_1129_);
    lean_ctor_set(v___x_1136_, 3, v___x_1134_);
    return v___x_1136_;
}
pub unsafe fn l_Lake_LeanLib_default(mut v_self_1137_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1138_ = lean_ctor_get(v_self_1137_, 0);
    v_name_1139_ = lean_ctor_get(v_self_1137_, 1);
    v_keyName_1140_ = lean_ctor_get(v_pkg_1138_, 2);
    v___x_1141_ = l_Lake_LeanLib_defaultFacet;
    lean_inc(v_name_1139_);
    lean_inc(v_keyName_1140_);
    v___x_1142_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1142_, 0, v_keyName_1140_);
    lean_ctor_set(v___x_1142_, 1, v_name_1139_);
    v___x_1143_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1144_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1144_, 0, v___x_1142_);
    lean_ctor_set(v___x_1144_, 1, v___x_1143_);
    lean_ctor_set(v___x_1144_, 2, v_self_1137_);
    lean_ctor_set(v___x_1144_, 3, v___x_1141_);
    return v___x_1144_;
}
pub unsafe fn l_Lake_LeanLib_modules(mut v_self_1145_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1146_ = lean_ctor_get(v_self_1145_, 0);
    v_name_1147_ = lean_ctor_get(v_self_1145_, 1);
    v_keyName_1148_ = lean_ctor_get(v_pkg_1146_, 2);
    v___x_1149_ = l_Lake_LeanLib_modulesFacet;
    lean_inc(v_name_1147_);
    lean_inc(v_keyName_1148_);
    v___x_1150_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1150_, 0, v_keyName_1148_);
    lean_ctor_set(v___x_1150_, 1, v_name_1147_);
    v___x_1151_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1152_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1152_, 0, v___x_1150_);
    lean_ctor_set(v___x_1152_, 1, v___x_1151_);
    lean_ctor_set(v___x_1152_, 2, v_self_1145_);
    lean_ctor_set(v___x_1152_, 3, v___x_1149_);
    return v___x_1152_;
}
pub unsafe fn l_Lake_LeanLib_leanArts(mut v_self_1153_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1154_ = lean_ctor_get(v_self_1153_, 0);
    v_name_1155_ = lean_ctor_get(v_self_1153_, 1);
    v_keyName_1156_ = lean_ctor_get(v_pkg_1154_, 2);
    v___x_1157_ = l_Lake_LeanLib_leanArtsFacet;
    lean_inc(v_name_1155_);
    lean_inc(v_keyName_1156_);
    v___x_1158_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1158_, 0, v_keyName_1156_);
    lean_ctor_set(v___x_1158_, 1, v_name_1155_);
    v___x_1159_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1160_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1160_, 0, v___x_1158_);
    lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    lean_ctor_set(v___x_1160_, 2, v_self_1153_);
    lean_ctor_set(v___x_1160_, 3, v___x_1157_);
    return v___x_1160_;
}
pub unsafe fn l_Lake_LeanLib_static(mut v_self_1161_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1162_ = lean_ctor_get(v_self_1161_, 0);
    v_name_1163_ = lean_ctor_get(v_self_1161_, 1);
    v_keyName_1164_ = lean_ctor_get(v_pkg_1162_, 2);
    v___x_1165_ = l_Lake_LeanLib_staticFacet;
    lean_inc(v_name_1163_);
    lean_inc(v_keyName_1164_);
    v___x_1166_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1166_, 0, v_keyName_1164_);
    lean_ctor_set(v___x_1166_, 1, v_name_1163_);
    v___x_1167_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1168_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1168_, 0, v___x_1166_);
    lean_ctor_set(v___x_1168_, 1, v___x_1167_);
    lean_ctor_set(v___x_1168_, 2, v_self_1161_);
    lean_ctor_set(v___x_1168_, 3, v___x_1165_);
    return v___x_1168_;
}
pub unsafe fn l_Lake_LeanLib_staticExport(mut v_self_1169_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1170_ = lean_ctor_get(v_self_1169_, 0);
    v_name_1171_ = lean_ctor_get(v_self_1169_, 1);
    v_keyName_1172_ = lean_ctor_get(v_pkg_1170_, 2);
    v___x_1173_ = l_Lake_LeanLib_staticExportFacet;
    lean_inc(v_name_1171_);
    lean_inc(v_keyName_1172_);
    v___x_1174_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1174_, 0, v_keyName_1172_);
    lean_ctor_set(v___x_1174_, 1, v_name_1171_);
    v___x_1175_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1176_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1176_, 0, v___x_1174_);
    lean_ctor_set(v___x_1176_, 1, v___x_1175_);
    lean_ctor_set(v___x_1176_, 2, v_self_1169_);
    lean_ctor_set(v___x_1176_, 3, v___x_1173_);
    return v___x_1176_;
}
pub unsafe fn l_Lake_LeanLib_shared(mut v_self_1177_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1178_ = lean_ctor_get(v_self_1177_, 0);
    v_name_1179_ = lean_ctor_get(v_self_1177_, 1);
    v_keyName_1180_ = lean_ctor_get(v_pkg_1178_, 2);
    v___x_1181_ = l_Lake_LeanLib_sharedFacet;
    lean_inc(v_name_1179_);
    lean_inc(v_keyName_1180_);
    v___x_1182_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1182_, 0, v_keyName_1180_);
    lean_ctor_set(v___x_1182_, 1, v_name_1179_);
    v___x_1183_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1184_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1184_, 0, v___x_1182_);
    lean_ctor_set(v___x_1184_, 1, v___x_1183_);
    lean_ctor_set(v___x_1184_, 2, v_self_1177_);
    lean_ctor_set(v___x_1184_, 3, v___x_1181_);
    return v___x_1184_;
}
pub unsafe fn l_Lake_LeanLib_extraDep(mut v_self_1185_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1186_ = lean_ctor_get(v_self_1185_, 0);
    v_name_1187_ = lean_ctor_get(v_self_1185_, 1);
    v_keyName_1188_ = lean_ctor_get(v_pkg_1186_, 2);
    v___x_1189_ = l_Lake_LeanLib_extraDepFacet;
    lean_inc(v_name_1187_);
    lean_inc(v_keyName_1188_);
    v___x_1190_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1190_, 0, v_keyName_1188_);
    lean_ctor_set(v___x_1190_, 1, v_name_1187_);
    v___x_1191_ = l_Lake_instDataKindLeanLib___closed__1;
    v___x_1192_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1192_, 0, v___x_1190_);
    lean_ctor_set(v___x_1192_, 1, v___x_1191_);
    lean_ctor_set(v___x_1192_, 2, v_self_1185_);
    lean_ctor_set(v___x_1192_, 3, v___x_1189_);
    return v___x_1192_;
}
pub unsafe fn l_Lake_LeanExe_facetCore(
    mut v_facet_1193_: *mut LeanObject,
    mut v_self_1194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1195_ = lean_ctor_get(v_self_1194_, 0);
    v_name_1196_ = lean_ctor_get(v_self_1194_, 1);
    v_keyName_1197_ = lean_ctor_get(v_pkg_1195_, 2);
    lean_inc(v_name_1196_);
    lean_inc(v_keyName_1197_);
    v___x_1198_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1198_, 0, v_keyName_1197_);
    lean_ctor_set(v___x_1198_, 1, v_name_1196_);
    v___x_1199_ = l_Lake_LeanExe_keyword;
    v___x_1200_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1200_, 0, v___x_1198_);
    lean_ctor_set(v___x_1200_, 1, v___x_1199_);
    lean_ctor_set(v___x_1200_, 2, v_self_1194_);
    lean_ctor_set(v___x_1200_, 3, v_facet_1193_);
    return v___x_1200_;
}
pub unsafe fn l_Lake_LeanExe_exe(mut v_self_1201_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1202_ = lean_ctor_get(v_self_1201_, 0);
    v_name_1203_ = lean_ctor_get(v_self_1201_, 1);
    v_keyName_1204_ = lean_ctor_get(v_pkg_1202_, 2);
    v___x_1205_ = l_Lake_LeanExe_exeFacet;
    lean_inc(v_name_1203_);
    lean_inc(v_keyName_1204_);
    v___x_1206_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1206_, 0, v_keyName_1204_);
    lean_ctor_set(v___x_1206_, 1, v_name_1203_);
    v___x_1207_ = l_Lake_LeanExe_keyword;
    v___x_1208_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1208_, 0, v___x_1206_);
    lean_ctor_set(v___x_1208_, 1, v___x_1207_);
    lean_ctor_set(v___x_1208_, 2, v_self_1201_);
    lean_ctor_set(v___x_1208_, 3, v___x_1205_);
    return v___x_1208_;
}
pub unsafe fn l_Lake_ExternLib_facetCore(
    mut v_facet_1209_: *mut LeanObject,
    mut v_self_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1211_ = lean_ctor_get(v_self_1210_, 0);
    v_name_1212_ = lean_ctor_get(v_self_1210_, 1);
    v_keyName_1213_ = lean_ctor_get(v_pkg_1211_, 2);
    lean_inc(v_name_1212_);
    lean_inc(v_keyName_1213_);
    v___x_1214_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1214_, 0, v_keyName_1213_);
    lean_ctor_set(v___x_1214_, 1, v_name_1212_);
    v___x_1215_ = l_Lake_ExternLib_keyword;
    v___x_1216_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1216_, 0, v___x_1214_);
    lean_ctor_set(v___x_1216_, 1, v___x_1215_);
    lean_ctor_set(v___x_1216_, 2, v_self_1210_);
    lean_ctor_set(v___x_1216_, 3, v_facet_1209_);
    return v___x_1216_;
}
pub unsafe fn l_Lake_ExternLib_static(mut v_self_1217_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1218_ = lean_ctor_get(v_self_1217_, 0);
    v_name_1219_ = lean_ctor_get(v_self_1217_, 1);
    v_keyName_1220_ = lean_ctor_get(v_pkg_1218_, 2);
    v___x_1221_ = l_Lake_ExternLib_staticFacet;
    lean_inc(v_name_1219_);
    lean_inc(v_keyName_1220_);
    v___x_1222_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1222_, 0, v_keyName_1220_);
    lean_ctor_set(v___x_1222_, 1, v_name_1219_);
    v___x_1223_ = l_Lake_ExternLib_keyword;
    v___x_1224_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1224_, 0, v___x_1222_);
    lean_ctor_set(v___x_1224_, 1, v___x_1223_);
    lean_ctor_set(v___x_1224_, 2, v_self_1217_);
    lean_ctor_set(v___x_1224_, 3, v___x_1221_);
    return v___x_1224_;
}
pub unsafe fn l_Lake_ExternLib_shared(mut v_self_1225_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1226_ = lean_ctor_get(v_self_1225_, 0);
    v_name_1227_ = lean_ctor_get(v_self_1225_, 1);
    v_keyName_1228_ = lean_ctor_get(v_pkg_1226_, 2);
    v___x_1229_ = l_Lake_ExternLib_sharedFacet;
    lean_inc(v_name_1227_);
    lean_inc(v_keyName_1228_);
    v___x_1230_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1230_, 0, v_keyName_1228_);
    lean_ctor_set(v___x_1230_, 1, v_name_1227_);
    v___x_1231_ = l_Lake_ExternLib_keyword;
    v___x_1232_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1232_, 0, v___x_1230_);
    lean_ctor_set(v___x_1232_, 1, v___x_1231_);
    lean_ctor_set(v___x_1232_, 2, v_self_1225_);
    lean_ctor_set(v___x_1232_, 3, v___x_1229_);
    return v___x_1232_;
}
pub unsafe fn l_Lake_ExternLib_dynlib(mut v_self_1233_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1234_ = lean_ctor_get(v_self_1233_, 0);
    v_name_1235_ = lean_ctor_get(v_self_1233_, 1);
    v_keyName_1236_ = lean_ctor_get(v_pkg_1234_, 2);
    v___x_1237_ = l_Lake_ExternLib_dynlibFacet;
    lean_inc(v_name_1235_);
    lean_inc(v_keyName_1236_);
    v___x_1238_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1238_, 0, v_keyName_1236_);
    lean_ctor_set(v___x_1238_, 1, v_name_1235_);
    v___x_1239_ = l_Lake_ExternLib_keyword;
    v___x_1240_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1240_, 0, v___x_1238_);
    lean_ctor_set(v___x_1240_, 1, v___x_1239_);
    lean_ctor_set(v___x_1240_, 2, v_self_1233_);
    lean_ctor_set(v___x_1240_, 3, v___x_1237_);
    return v___x_1240_;
}
pub unsafe fn l_Lake_InputFile_facetCore(
    mut v_facet_1241_: *mut LeanObject,
    mut v_self_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1243_ = lean_ctor_get(v_self_1242_, 0);
    v_name_1244_ = lean_ctor_get(v_self_1242_, 1);
    v_keyName_1245_ = lean_ctor_get(v_pkg_1243_, 2);
    lean_inc(v_name_1244_);
    lean_inc(v_keyName_1245_);
    v___x_1246_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1246_, 0, v_keyName_1245_);
    lean_ctor_set(v___x_1246_, 1, v_name_1244_);
    v___x_1247_ = l_Lake_InputFile_keyword;
    v___x_1248_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1248_, 0, v___x_1246_);
    lean_ctor_set(v___x_1248_, 1, v___x_1247_);
    lean_ctor_set(v___x_1248_, 2, v_self_1242_);
    lean_ctor_set(v___x_1248_, 3, v_facet_1241_);
    return v___x_1248_;
}
pub unsafe fn l_Lake_InputFile_default(mut v_self_1249_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1250_ = lean_ctor_get(v_self_1249_, 0);
    v_name_1251_ = lean_ctor_get(v_self_1249_, 1);
    v_keyName_1252_ = lean_ctor_get(v_pkg_1250_, 2);
    v___x_1253_ = l_Lake_InputFile_defaultFacet;
    lean_inc(v_name_1251_);
    lean_inc(v_keyName_1252_);
    v___x_1254_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1254_, 0, v_keyName_1252_);
    lean_ctor_set(v___x_1254_, 1, v_name_1251_);
    v___x_1255_ = l_Lake_InputFile_keyword;
    v___x_1256_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1256_, 0, v___x_1254_);
    lean_ctor_set(v___x_1256_, 1, v___x_1255_);
    lean_ctor_set(v___x_1256_, 2, v_self_1249_);
    lean_ctor_set(v___x_1256_, 3, v___x_1253_);
    return v___x_1256_;
}
pub unsafe fn l_Lake_InputDir_facetCore(
    mut v_facet_1257_: *mut LeanObject,
    mut v_self_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pkg_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1259_ = lean_ctor_get(v_self_1258_, 0);
    v_name_1260_ = lean_ctor_get(v_self_1258_, 1);
    v_keyName_1261_ = lean_ctor_get(v_pkg_1259_, 2);
    lean_inc(v_name_1260_);
    lean_inc(v_keyName_1261_);
    v___x_1262_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1262_, 0, v_keyName_1261_);
    lean_ctor_set(v___x_1262_, 1, v_name_1260_);
    v___x_1263_ = l_Lake_InputDir_keyword;
    v___x_1264_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1264_, 0, v___x_1262_);
    lean_ctor_set(v___x_1264_, 1, v___x_1263_);
    lean_ctor_set(v___x_1264_, 2, v_self_1258_);
    lean_ctor_set(v___x_1264_, 3, v_facet_1257_);
    return v___x_1264_;
}
pub unsafe fn l_Lake_InputDir_default(mut v_self_1265_: *mut LeanObject) -> *mut LeanObject {
    let mut v_pkg_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    v_pkg_1266_ = lean_ctor_get(v_self_1265_, 0);
    v_name_1267_ = lean_ctor_get(v_self_1265_, 1);
    v_keyName_1268_ = lean_ctor_get(v_pkg_1266_, 2);
    v___x_1269_ = l_Lake_InputDir_defaultFacet;
    lean_inc(v_name_1267_);
    lean_inc(v_keyName_1268_);
    v___x_1270_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1270_, 0, v_keyName_1268_);
    lean_ctor_set(v___x_1270_, 1, v_name_1267_);
    v___x_1271_ = l_Lake_InputDir_keyword;
    v___x_1272_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_1272_, 0, v___x_1270_);
    lean_ctor_set(v___x_1272_, 1, v___x_1271_);
    lean_ctor_set(v___x_1272_, 2, v_self_1265_);
    lean_ctor_set(v___x_1272_, 3, v___x_1269_);
    return v___x_1272_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Infos(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Info(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Infos(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Build_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Infos(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Info(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanExe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_ExternLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_InputFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Infos(builtin);
}
