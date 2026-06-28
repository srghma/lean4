// Lean compiler output
// Module: Lake.Build.Facets
// Imports: Lake.Build.Job.Basic Lake.Build.ModuleArtifacts Lake.Build.Data
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4};
use crate::r#gen::Lake::Build::Data::{
    initialize_Lake_Build_Data, runtime_initialize_Lake_Build_Data,
};
use crate::r#gen::Lake::Build::Job::Basic::{
    initialize_Lake_Build_Job_Basic, runtime_initialize_Lake_Build_Job_Basic,
};
use crate::r#gen::Lake::Build::ModuleArtifacts::{
    initialize_Lake_Build_ModuleArtifacts, runtime_initialize_Lake_Build_ModuleArtifacts,
};
use crate::r#gen::Lake::Build::Trace::l_Lake_BuildTrace_nil;
use crate::r#gen::Lean::Setup::l_Lean_instInhabitedImportArtifacts_default;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__1_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__10_value:
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
    m_data: [100, 97, 116, 97, 95, 101, 113, 0],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__12_value:
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
    m_data: [95, 0],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__14_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__17_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprModuleFacet_repr___redArg___closed__18_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instReprModuleFacet_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprModuleFacet_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_leanFacet___closed__0_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lake_Module_leanFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_leanFacet___closed__1_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_Module_leanFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_leanFacet___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_leanFacet___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16876227222941795311 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_leanFacet___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__2_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_leanFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_headerFacet___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [104, 101, 97, 100, 101, 114, 0],
    };
static mut l_Lake_Module_headerFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_headerFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_headerFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_headerFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_headerFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_headerFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18259336816223673424 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_headerFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_headerFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_headerFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_headerFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_setupFacet___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [115, 101, 116, 117, 112, 0],
    };
static mut l_Lake_Module_setupFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_setupFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_setupFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_setupFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_setupFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_setupFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            456020564110926443 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_setupFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_setupFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_setupFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_setupFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_depsFacet___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_Module_depsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_depsFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_depsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_depsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_depsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_depsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6835673281855179039 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_depsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_depsFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_depsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_depsFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedModuleImportInfo_default___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [60, 110, 105, 108, 62, 0],
};
static mut l_Lake_instInhabitedModuleImportInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedModuleImportInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedModuleImportInfo_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedModuleImportInfo_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedModuleImportInfo_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedModuleImportInfo_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedModuleImportInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedModuleImportInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Module_importInfoFacet___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [105, 109, 112, 111, 114, 116, 73, 110, 102, 111, 0],
    };
static mut l_Lake_Module_importInfoFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importInfoFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_importInfoFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_importInfoFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_importInfoFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_importInfoFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15596283097066696856 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_importInfoFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importInfoFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_importInfoFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importInfoFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedModuleExportInfo_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedModuleExportInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedModuleExportInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedModuleExportInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Module_exportInfoFacet___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [101, 120, 112, 111, 114, 116, 73, 110, 102, 111, 0],
    };
static mut l_Lake_Module_exportInfoFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_exportInfoFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_exportInfoFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_exportInfoFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_exportInfoFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_exportInfoFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16200670956876917164 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_exportInfoFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_exportInfoFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_exportInfoFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_exportInfoFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_importArtsFacet___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [105, 109, 112, 111, 114, 116, 65, 114, 116, 115, 0],
    };
static mut l_Lake_Module_importArtsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importArtsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_importArtsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_importArtsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_importArtsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_importArtsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3697790974813496574 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_importArtsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importArtsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_importArtsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importArtsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_importAllArtsFacet___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            105, 109, 112, 111, 114, 116, 65, 108, 108, 65, 114, 116, 115, 0,
        ],
    };
static mut l_Lake_Module_importAllArtsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importAllArtsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_importAllArtsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_importAllArtsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_importAllArtsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_importAllArtsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8491393228094715903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_importAllArtsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importAllArtsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_importAllArtsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_importAllArtsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_leanArtsFacet___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [108, 101, 97, 110, 65, 114, 116, 115, 0],
    };
static mut l_Lake_Module_leanArtsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanArtsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_leanArtsFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_leanArtsFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanArtsFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_leanArtsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6679281075288713164 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_leanArtsFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanArtsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_leanArtsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanArtsFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_ltarFacet___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [108, 116, 97, 114, 0],
    };
static mut l_Lake_Module_ltarFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ltarFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_ltarFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_ltarFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_ltarFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_ltarFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11830009830656929090 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_ltarFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ltarFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_ltarFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ltarFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_oleanFacet___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [111, 108, 101, 97, 110, 0],
    };
static mut l_Lake_Module_oleanFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_oleanFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_oleanFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oleanFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_oleanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4879834933641764490 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_oleanFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_oleanFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_oleanServerFacet___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 101, 114, 118, 101, 114, 0],
    };
static mut l_Lake_Module_oleanServerFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanServerFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_oleanServerFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_oleanServerFacet___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oleanServerFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_oleanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4879834933641764490 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_oleanServerFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oleanServerFacet___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_oleanServerFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13935991689217861332 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_oleanServerFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanServerFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_oleanServerFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanServerFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_oleanPrivateFacet___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 114, 105, 118, 97, 116, 101, 0],
    };
static mut l_Lake_Module_oleanPrivateFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanPrivateFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_oleanPrivateFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_oleanPrivateFacet___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oleanPrivateFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_oleanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4879834933641764490 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_oleanPrivateFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oleanPrivateFacet___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_oleanPrivateFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13837370152730653153 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_oleanPrivateFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanPrivateFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_oleanPrivateFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanPrivateFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_ileanFacet___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 108, 101, 97, 110, 0],
    };
static mut l_Lake_Module_ileanFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ileanFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_ileanFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_ileanFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_ileanFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_ileanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12257272929744626026 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_ileanFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ileanFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_ileanFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ileanFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_irFacet___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [105, 114, 0],
    };
static mut l_Lake_Module_irFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_irFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_irFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_irFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_irFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_irFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            475808579159540105 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_irFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_irFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_irFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_irFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_cFacet___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [99, 0],
    };
static mut l_Lake_Module_cFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_cFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_cFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_cFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_cFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_cFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13216261639980310762 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_cFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_cFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_cFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_cFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_bcFacet___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [98, 99, 0],
    };
static mut l_Lake_Module_bcFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_bcFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_bcFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_bcFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_bcFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12806604851717884005 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_bcFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_bcFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_coFacet___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [111, 0],
    };
static mut l_Lake_Module_coFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_coFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_coFacet___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_cFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13216261639980310762 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_coFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2322625525455626942 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_coFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_coFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_coExportFacet___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [101, 120, 112, 111, 114, 116, 0],
    };
static mut l_Lake_Module_coExportFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_coExportFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_coExportFacet___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_cFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13216261639980310762 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_coExportFacet___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2322625525455626942 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_coExportFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4233807925756889726 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_coExportFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_coExportFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_coNoExportFacet___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [110, 111, 101, 120, 112, 111, 114, 116, 0],
    };
static mut l_Lake_Module_coNoExportFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coNoExportFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_coNoExportFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_coNoExportFacet___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_coNoExportFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_cFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13216261639980310762 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_coNoExportFacet___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_coNoExportFacet___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2322625525455626942 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_coNoExportFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_coNoExportFacet___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coNoExportFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5071495246046566772 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_coNoExportFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coNoExportFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_coNoExportFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coNoExportFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_bcoFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_bcoFacet___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_bcoFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_bcFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12806604851717884005 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_bcoFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_bcoFacet___closed__0_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4167703427655315965 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_bcoFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcoFacet___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_bcoFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcoFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_oFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_oFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12460118195153313655 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_oFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oFacet___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_oFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_Module_oExportFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_oExportFacet___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oExportFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12460118195153313655 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_oExportFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oExportFacet___closed__0_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9793307277605326715 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_oExportFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oExportFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_oExportFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oExportFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Module_oNoExportFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_leanFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5134674735115079031 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Module_oNoExportFacet___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oNoExportFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12460118195153313655 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Module_oNoExportFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Module_oNoExportFacet___closed__0_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coNoExportFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15187366159672136561 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Module_oNoExportFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oNoExportFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_oNoExportFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oNoExportFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_optBuildCacheFacet___closed__0_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lake_Package_optBuildCacheFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_optBuildCacheFacet___closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [111, 112, 116, 67, 97, 99, 104, 101, 0],
    };
static mut l_Lake_Package_optBuildCacheFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_optBuildCacheFacet___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6671755061125946191 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Package_optBuildCacheFacet___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7066318727923133376 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_optBuildCacheFacet___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_optBuildCacheFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_buildCacheFacet___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 97, 99, 104, 101, 0],
    };
static mut l_Lake_Package_buildCacheFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_buildCacheFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_buildCacheFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6671755061125946191 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Package_buildCacheFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_buildCacheFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_buildCacheFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12381640387684173302 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_buildCacheFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_buildCacheFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_buildCacheFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_buildCacheFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_optReservoirBarrelFacet___closed__0_value:
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
    m_data: [111, 112, 116, 66, 97, 114, 114, 101, 108, 0],
};
static mut l_Lake_Package_optReservoirBarrelFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optReservoirBarrelFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_optReservoirBarrelFacet___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6671755061125946191 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_Package_optReservoirBarrelFacet___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_Package_optReservoirBarrelFacet___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Package_optReservoirBarrelFacet___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11527174434512684849 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_Package_optReservoirBarrelFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optReservoirBarrelFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_optReservoirBarrelFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optReservoirBarrelFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_reservoirBarrelFacet___closed__0_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [98, 97, 114, 114, 101, 108, 0],
};
static mut l_Lake_Package_reservoirBarrelFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_reservoirBarrelFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_reservoirBarrelFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6671755061125946191 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_Package_reservoirBarrelFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_reservoirBarrelFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_reservoirBarrelFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16270329459033210006 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_reservoirBarrelFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_reservoirBarrelFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_reservoirBarrelFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_reservoirBarrelFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_optGitHubReleaseFacet___closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [111, 112, 116, 82, 101, 108, 101, 97, 115, 101, 0],
};
static mut l_Lake_Package_optGitHubReleaseFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optGitHubReleaseFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_optGitHubReleaseFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6671755061125946191 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_Package_optGitHubReleaseFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_optGitHubReleaseFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_optGitHubReleaseFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6842613154372138779 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_optGitHubReleaseFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optGitHubReleaseFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_optGitHubReleaseFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_optGitHubReleaseFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_gitHubReleaseFacet___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [114, 101, 108, 101, 97, 115, 101, 0],
    };
static mut l_Lake_Package_gitHubReleaseFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_gitHubReleaseFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_gitHubReleaseFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6671755061125946191 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Package_gitHubReleaseFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_gitHubReleaseFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_gitHubReleaseFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17458469103833848464 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_gitHubReleaseFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_gitHubReleaseFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_gitHubReleaseFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_gitHubReleaseFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_extraDepFacet___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [101, 120, 116, 114, 97, 68, 101, 112, 0],
    };
static mut l_Lake_Package_extraDepFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_extraDepFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Package_extraDepFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_optBuildCacheFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6671755061125946191 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Package_extraDepFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Package_extraDepFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_extraDepFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6117400162057056510 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_extraDepFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_extraDepFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_extraDepFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_extraDepFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLib_defaultFacet___closed__0_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lake_LeanLib_defaultFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLib_defaultFacet___closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 102, 97, 117, 108, 116, 0],
    };
static mut l_Lake_LeanLib_defaultFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_LeanLib_defaultFacet___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanLib_defaultFacet___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__1_value)
                as *mut crate::leanh::LeanObject,
            17152956876580337925 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_defaultFacet___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanLib_defaultFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_LeanLib_leanArtsFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanLib_leanArtsFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_leanArtsFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_leanArtsFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4219749841062391336 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_leanArtsFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_leanArtsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanLib_leanArtsFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_leanArtsFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLib_staticFacet___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 116, 97, 116, 105, 99, 0],
    };
static mut l_Lake_LeanLib_staticFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_LeanLib_staticFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanLib_staticFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_staticFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_staticFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16705970262735172796 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_staticFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanLib_staticFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_LeanLib_staticExportFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_LeanLib_staticExportFacet___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_staticExportFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_staticFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16705970262735172796 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanLib_staticExportFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_staticExportFacet___closed__0_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Module_coExportFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5003722531946061140 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_staticExportFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticExportFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanLib_staticExportFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_staticExportFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLib_sharedFacet___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 104, 97, 114, 101, 100, 0],
    };
static mut l_Lake_LeanLib_sharedFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_sharedFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_LeanLib_sharedFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanLib_sharedFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_sharedFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_sharedFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14601067066221635802 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_sharedFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_sharedFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanLib_sharedFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_sharedFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_LeanLib_extraDepFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanLib_extraDepFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanLib_extraDepFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_extraDepFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3591474355028748786 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLib_extraDepFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_extraDepFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanLib_extraDepFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_extraDepFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExe_defaultFacet___closed__0_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lake_LeanExe_defaultFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_defaultFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_LeanExe_defaultFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExe_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10587356296225942211 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanExe_defaultFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExe_defaultFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__1_value)
                as *mut crate::leanh::LeanObject,
            2109283824164984549 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExe_defaultFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanExe_defaultFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExe_exeFacet___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [101, 120, 101, 0],
    };
static mut l_Lake_LeanExe_exeFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_exeFacet___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_LeanExe_exeFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExe_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10587356296225942211 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_LeanExe_exeFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExe_exeFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExe_exeFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12491672165995728147 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExe_exeFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_exeFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_LeanExe_exeFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExe_exeFacet___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_ExternLib_defaultFacet___closed__0_value: crate::leanh::LeanStringObject<11> =
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
static mut l_Lake_ExternLib_defaultFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_defaultFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_ExternLib_defaultFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ExternLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11562366611225967008 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_ExternLib_defaultFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ExternLib_defaultFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__1_value)
                as *mut crate::leanh::LeanObject,
            603358037820008282 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ExternLib_defaultFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_ExternLib_defaultFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_ExternLib_staticFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ExternLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11562366611225967008 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_ExternLib_staticFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ExternLib_staticFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_staticFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14684070100483676091 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ExternLib_staticFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_staticFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_ExternLib_staticFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_staticFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_ExternLib_sharedFacet___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ExternLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11562366611225967008 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_ExternLib_sharedFacet___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ExternLib_sharedFacet___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_sharedFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5725707611134092677 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ExternLib_sharedFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_sharedFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_ExternLib_sharedFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_sharedFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_ExternLib_dynlibFacet___closed__0_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lake_ExternLib_dynlibFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_dynlibFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_ExternLib_dynlibFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ExternLib_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11562366611225967008 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_ExternLib_dynlibFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_ExternLib_dynlibFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_ExternLib_dynlibFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14229952403475611671 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_ExternLib_dynlibFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_dynlibFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_ExternLib_dynlibFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ExternLib_dynlibFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFile_defaultFacet___closed__0_value: crate::leanh::LeanStringObject<11> =
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
static mut l_Lake_InputFile_defaultFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_defaultFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_InputFile_defaultFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputFile_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4067501922346325234 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_InputFile_defaultFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputFile_defaultFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__1_value)
                as *mut crate::leanh::LeanObject,
            2232289837151155360 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputFile_defaultFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_InputFile_defaultFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFile_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDir_defaultFacet___closed__0_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Lake_InputDir_defaultFacet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_defaultFacet___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_InputDir_defaultFacet___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputDir_defaultFacet___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9710019104504222840 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_InputDir_defaultFacet___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputDir_defaultFacet___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLib_defaultFacet___closed__1_value)
                as *mut crate::leanh::LeanObject,
            12486016758454656754 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputDir_defaultFacet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_InputDir_defaultFacet: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDir_defaultFacet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_instReprModuleFacet_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_342_ = lean_nat_to_int(v___x_341_);
    return v___x_342_;
}
pub unsafe fn _init_l_Lake_instReprModuleFacet_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = l_Lake_instReprModuleFacet_repr___redArg___closed__0;
    v___x_354_ = lean_string_length(v___x_353_);
    return v___x_354_;
}
pub unsafe fn _init_l_Lake_instReprModuleFacet_repr___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprModuleFacet_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lake_instReprModuleFacet_repr___redArg___closed__15_once),
        _init_l_Lake_instReprModuleFacet_repr___redArg___closed__15,
    );
    v___x_356_ = lean_nat_to_int(v___x_355_);
    return v___x_356_;
}
pub unsafe fn l_Lake_instReprModuleFacet_repr___redArg(
    mut v_x_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: u8 = 0;
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = l_Lake_instReprModuleFacet_repr___redArg___closed__5;
    v___x_363_ = l_Lake_instReprModuleFacet_repr___redArg___closed__6;
    v___x_364_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprModuleFacet_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprModuleFacet_repr___redArg___closed__7_once),
        _init_l_Lake_instReprModuleFacet_repr___redArg___closed__7,
    );
    v___x_365_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_366_ = l_Lean_Name_reprPrec(v_x_361_, v___x_365_);
    v___x_367_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_367_, 0, v___x_364_);
    crate::leanh::lean_ctor_set(v___x_367_, 1, v___x_366_);
    v___x_368_ = 0;
    v___x_369_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_369_, 0, v___x_367_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_369_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_368_,
    );
    v___x_370_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_370_, 0, v___x_363_);
    crate::leanh::lean_ctor_set(v___x_370_, 1, v___x_369_);
    v___x_371_ = l_Lake_instReprModuleFacet_repr___redArg___closed__9;
    v___x_372_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_372_, 0, v___x_370_);
    crate::leanh::lean_ctor_set(v___x_372_, 1, v___x_371_);
    v___x_373_ = crate::leanh::lean_box(1);
    v___x_374_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_374_, 0, v___x_372_);
    crate::leanh::lean_ctor_set(v___x_374_, 1, v___x_373_);
    v___x_375_ = l_Lake_instReprModuleFacet_repr___redArg___closed__11;
    v___x_376_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_376_, 0, v___x_374_);
    crate::leanh::lean_ctor_set(v___x_376_, 1, v___x_375_);
    v___x_377_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_377_, 0, v___x_376_);
    crate::leanh::lean_ctor_set(v___x_377_, 1, v___x_362_);
    v___x_378_ = l_Lake_instReprModuleFacet_repr___redArg___closed__13;
    v___x_379_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_379_, 0, v___x_377_);
    crate::leanh::lean_ctor_set(v___x_379_, 1, v___x_378_);
    v___x_380_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprModuleFacet_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprModuleFacet_repr___redArg___closed__16_once),
        _init_l_Lake_instReprModuleFacet_repr___redArg___closed__16,
    );
    v___x_381_ = l_Lake_instReprModuleFacet_repr___redArg___closed__17;
    v___x_382_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_382_, 0, v___x_381_);
    crate::leanh::lean_ctor_set(v___x_382_, 1, v___x_379_);
    v___x_383_ = l_Lake_instReprModuleFacet_repr___redArg___closed__18;
    v___x_384_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_384_, 0, v___x_382_);
    crate::leanh::lean_ctor_set(v___x_384_, 1, v___x_383_);
    v___x_385_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_385_, 0, v___x_380_);
    crate::leanh::lean_ctor_set(v___x_385_, 1, v___x_384_);
    v___x_386_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_386_, 0, v___x_385_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_386_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_368_,
    );
    return v___x_386_;
}
pub unsafe fn l_Lake_instReprModuleFacet_repr(
    mut v_00_u03b1_387_: *mut crate::leanh::LeanObject,
    mut v_inst_388_: *mut crate::leanh::LeanObject,
    mut v_x_389_: *mut crate::leanh::LeanObject,
    mut v_prec_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = l_Lake_instReprModuleFacet_repr___redArg(v_x_389_);
    return v___x_391_;
}
pub unsafe fn l_Lake_instReprModuleFacet_repr___boxed(
    mut v_00_u03b1_392_: *mut crate::leanh::LeanObject,
    mut v_inst_393_: *mut crate::leanh::LeanObject,
    mut v_x_394_: *mut crate::leanh::LeanObject,
    mut v_prec_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_396_ =
        l_Lake_instReprModuleFacet_repr(v_00_u03b1_392_, v_inst_393_, v_x_394_, v_prec_395_);
    crate::leanh::lean_dec(v_prec_395_);
    crate::leanh::lean_dec_ref(v_inst_393_);
    return v_res_396_;
}
pub unsafe fn l_Lake_instReprModuleFacet___redArg(
    mut v_inst_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = crate::leanh::lean_alloc_closure(
        l_Lake_instReprModuleFacet_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_398_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_398_, 1, v_inst_397_);
    return v___x_398_;
}
pub unsafe fn l_Lake_instReprModuleFacet(
    mut v_00_u03b1_399_: *mut crate::leanh::LeanObject,
    mut v_inst_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = crate::leanh::lean_alloc_closure(
        l_Lake_instReprModuleFacet_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_401_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_401_, 1, v_inst_400_);
    return v___x_401_;
}
pub unsafe fn l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg(
    mut v_facet_402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_facet_402_);
    return v_facet_402_;
}
pub unsafe fn l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg___boxed(
    mut v_facet_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_404_ = l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg(v_facet_403_);
    crate::leanh::lean_dec(v_facet_403_);
    return v_res_404_;
}
pub unsafe fn l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut(
    mut v_facet_405_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_facet_405_);
    return v_facet_405_;
}
pub unsafe fn l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___boxed(
    mut v_facet_408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_409_: *mut crate::leanh::LeanObject,
    mut v_inst_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut(
        v_facet_408_,
        v_00_u03b1_409_,
        v_inst_410_,
    );
    crate::leanh::lean_dec(v_facet_408_);
    return v_res_411_;
}
pub unsafe fn _init_l_Lake_instInhabitedModuleImportInfo_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = l_Lake_instInhabitedModuleImportInfo_default___closed__0;
    v___x_435_ = l_Lake_BuildTrace_nil(v___x_434_);
    return v___x_435_;
}
pub unsafe fn _init_l_Lake_instInhabitedModuleImportInfo_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedModuleImportInfo_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedModuleImportInfo_default___closed__1_once),
        _init_l_Lake_instInhabitedModuleImportInfo_default___closed__1,
    );
    v___x_437_ = crate::leanh::lean_box(1);
    v___x_438_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_438_, 0, v___x_437_);
    crate::leanh::lean_ctor_set(v___x_438_, 1, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_438_, 2, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_438_, 3, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_438_, 4, v___x_436_);
    crate::leanh::lean_ctor_set(v___x_438_, 5, v___x_436_);
    return v___x_438_;
}
pub unsafe fn _init_l_Lake_instInhabitedModuleImportInfo_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedModuleImportInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedModuleImportInfo_default___closed__2_once),
        _init_l_Lake_instInhabitedModuleImportInfo_default___closed__2,
    );
    return v___x_439_;
}
pub unsafe fn _init_l_Lake_instInhabitedModuleImportInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ = l_Lake_instInhabitedModuleImportInfo_default;
    return v___x_440_;
}
pub unsafe fn _init_l_Lake_instInhabitedModuleExportInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Lean_instInhabitedImportArtifacts_default;
    v___x_447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedModuleImportInfo_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedModuleImportInfo_default___closed__1_once),
        _init_l_Lake_instInhabitedModuleImportInfo_default___closed__1,
    );
    v___x_448_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_448_, 0, v___x_447_);
    crate::leanh::lean_ctor_set(v___x_448_, 1, v___x_446_);
    crate::leanh::lean_ctor_set(v___x_448_, 2, v___x_447_);
    crate::leanh::lean_ctor_set(v___x_448_, 3, v___x_447_);
    crate::leanh::lean_ctor_set(v___x_448_, 4, v___x_446_);
    crate::leanh::lean_ctor_set(v___x_448_, 5, v___x_447_);
    crate::leanh::lean_ctor_set(v___x_448_, 6, v___x_447_);
    crate::leanh::lean_ctor_set(v___x_448_, 7, v___x_447_);
    crate::leanh::lean_ctor_set(v___x_448_, 8, v___x_447_);
    crate::leanh::lean_ctor_set(v___x_448_, 9, v___x_447_);
    return v___x_448_;
}
pub unsafe fn _init_l_Lake_instInhabitedModuleExportInfo_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedModuleExportInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedModuleExportInfo_default___closed__0_once),
        _init_l_Lake_instInhabitedModuleExportInfo_default___closed__0,
    );
    return v___x_449_;
}
pub unsafe fn _init_l_Lake_instInhabitedModuleExportInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_450_ = l_Lake_instInhabitedModuleExportInfo_default;
    return v___x_450_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Facets(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Job_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_ModuleArtifacts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instInhabitedModuleImportInfo_default =
        _init_l_Lake_instInhabitedModuleImportInfo_default();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedModuleImportInfo_default);
    l_Lake_instInhabitedModuleImportInfo = _init_l_Lake_instInhabitedModuleImportInfo();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedModuleImportInfo);
    l_Lake_instInhabitedModuleExportInfo_default =
        _init_l_Lake_instInhabitedModuleExportInfo_default();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedModuleExportInfo_default);
    l_Lake_instInhabitedModuleExportInfo = _init_l_Lake_instInhabitedModuleExportInfo();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedModuleExportInfo);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Facets(builtin: u8) -> *mut crate::leanh::LeanObject {
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
pub unsafe fn initialize_Lake_Build_Facets(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Job_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_ModuleArtifacts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Facets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Facets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Facets(builtin);
}
