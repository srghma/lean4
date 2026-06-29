// Lean compiler output
// Module: Init.Grind.Util
// Imports: Init.Data.Cast Init.Grind.Tactics Init.Grind.Tactics Init.Classical
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Cast::{
    initialize_Init_Data_Cast, runtime_initialize_Init_Data_Cast,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node5,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
pub static l_Lean_Grind_nestedProofUnexpander___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Grind_nestedProofUnexpander___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nestedProofUnexpander___closed__1_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Grind_nestedProofUnexpander___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nestedProofUnexpander___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Grind_nestedProofUnexpander___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nestedProofUnexpander___closed__3_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [97, 112, 112, 0],
    };
static mut l_Lean_Grind_nestedProofUnexpander___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Grind_nestedProofUnexpander___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12966880221525079621 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_nestedProofUnexpander___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nestedProofUnexpander___closed__5_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 7,
    m_data: [116, 101, 114, 109, 226, 128, 185, 95, 226, 128, 186, 0],
};
static mut l_Lean_Grind_nestedProofUnexpander___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nestedProofUnexpander___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__5_value)
                as *mut crate::leanh::LeanObject,
            8315864120963730325 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_nestedProofUnexpander___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nestedProofUnexpander___closed__7_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 128, 185, 0],
    };
static mut l_Lean_Grind_nestedProofUnexpander___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nestedProofUnexpander___closed__8_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 128, 186, 0],
    };
static mut l_Lean_Grind_nestedProofUnexpander___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_eqMatchUnexpander___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 61, 95, 0],
    };
static mut l_Lean_Grind_eqMatchUnexpander___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_eqMatchUnexpander___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_eqMatchUnexpander___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Grind_eqMatchUnexpander___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5677895497334651815 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_eqMatchUnexpander___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_eqMatchUnexpander___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_eqMatchUnexpander___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [61, 0],
    };
static mut l_Lean_Grind_eqMatchUnexpander___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_eqMatchUnexpander___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_offsetUnexpander___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 43, 95, 0],
    };
static mut l_Lean_Grind_offsetUnexpander___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_offsetUnexpander___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_offsetUnexpander___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Grind_offsetUnexpander___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8601847764421812281 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_offsetUnexpander___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_offsetUnexpander___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_offsetUnexpander___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [43, 0],
    };
static mut l_Lean_Grind_offsetUnexpander___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_offsetUnexpander___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_natCastUnexpander___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [99, 111, 101, 78, 111, 116, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Grind_natCastUnexpander___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_natCastUnexpander___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_natCastUnexpander___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Grind_natCastUnexpander___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4193428478068483112 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_natCastUnexpander___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_natCastUnexpander___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_natCastUnexpander___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 134, 145, 0],
    };
static mut l_Lean_Grind_natCastUnexpander___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_natCastUnexpander___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_markerUnexpander___redArg___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16173796135615239867 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__2_value:
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
    m_data: [98, 121, 0],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__3_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__4_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_markerUnexpander___redArg___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_markerUnexpander___redArg___closed__7_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__9_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__10_value:
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
    m_data: [103, 114, 105, 110, 100, 0],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_markerUnexpander___redArg___closed__11_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        7213727686127018646 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_markerUnexpander___redArg___closed__12_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nestedProofUnexpander___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_markerUnexpander___redArg___closed__13_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__13_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_markerUnexpander___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_markerUnexpander___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_markerUnexpander___redArg___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_markerUnexpander___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_nestedDecidable___redArg(mut v_h_267_: u8) -> u8 {
    return v_h_267_;
}
pub unsafe fn l_Lean_Grind_nestedDecidable___redArg___boxed(
    mut v_h_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_269_: u8 = 0;
    let mut v_res_270_: u8 = 0;
    let mut v_r_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_269_ = (crate::leanh::lean_unbox(v_h_268_) as u8);
    v_res_270_ = l_Lean_Grind_nestedDecidable___redArg(v_h_boxed_269_);
    v_r_271_ = crate::leanh::lean_box((v_res_270_) as usize);
    return v_r_271_;
}
pub unsafe fn l_Lean_Grind_nestedDecidable(
    mut v_p_272_: *mut crate::leanh::LeanObject,
    mut v_h_273_: u8,
) -> u8 {
    return v_h_273_;
}
pub unsafe fn l_Lean_Grind_nestedDecidable___boxed(
    mut v_p_274_: *mut crate::leanh::LeanObject,
    mut v_h_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_276_: u8 = 0;
    let mut v_res_277_: u8 = 0;
    let mut v_r_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_276_ = (crate::leanh::lean_unbox(v_h_275_) as u8);
    v_res_277_ = l_Lean_Grind_nestedDecidable(v_p_274_, v_h_boxed_276_);
    v_r_278_ = crate::leanh::lean_box((v_res_277_) as usize);
    return v_r_278_;
}
pub unsafe fn l_Lean_Grind_simpMatchDiscrsOnly___redArg(
    mut v_a_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_279_);
    return v_a_279_;
}
pub unsafe fn l_Lean_Grind_simpMatchDiscrsOnly___redArg___boxed(
    mut v_a_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_281_ = l_Lean_Grind_simpMatchDiscrsOnly___redArg(v_a_280_);
    crate::leanh::lean_dec(v_a_280_);
    return v_res_281_;
}
pub unsafe fn l_Lean_Grind_simpMatchDiscrsOnly(
    mut v_00_u03b1_282_: *mut crate::leanh::LeanObject,
    mut v_a_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_283_);
    return v_a_283_;
}
pub unsafe fn l_Lean_Grind_simpMatchDiscrsOnly___boxed(
    mut v_00_u03b1_284_: *mut crate::leanh::LeanObject,
    mut v_a_285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Lean_Grind_simpMatchDiscrsOnly(v_00_u03b1_284_, v_a_285_);
    crate::leanh::lean_dec(v_a_285_);
    return v_res_286_;
}
pub unsafe fn l_Lean_Grind_abstractFn___redArg(
    mut v_a_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_287_);
    return v_a_287_;
}
pub unsafe fn l_Lean_Grind_abstractFn___redArg___boxed(
    mut v_a_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Lean_Grind_abstractFn___redArg(v_a_288_);
    crate::leanh::lean_dec(v_a_288_);
    return v_res_289_;
}
pub unsafe fn l_Lean_Grind_abstractFn(
    mut v_00_u03b1_290_: *mut crate::leanh::LeanObject,
    mut v_a_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_291_);
    return v_a_291_;
}
pub unsafe fn l_Lean_Grind_abstractFn___boxed(
    mut v_00_u03b1_292_: *mut crate::leanh::LeanObject,
    mut v_a_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Lean_Grind_abstractFn(v_00_u03b1_292_, v_a_293_);
    crate::leanh::lean_dec(v_a_293_);
    return v_res_294_;
}
pub unsafe fn l_Lean_Grind_offset(
    mut v_a_295_: *mut crate::leanh::LeanObject,
    mut v_b_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = lean_nat_add(v_a_295_, v_b_296_);
    return v___x_297_;
}
pub unsafe fn l_Lean_Grind_offset___boxed(
    mut v_a_298_: *mut crate::leanh::LeanObject,
    mut v_b_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Lean_Grind_offset(v_a_298_, v_b_299_);
    crate::leanh::lean_dec(v_b_299_);
    crate::leanh::lean_dec(v_a_298_);
    return v_res_300_;
}
pub unsafe fn l_Lean_Grind_nestedProofUnexpander(
    mut v_stx_315_: *mut crate::leanh::LeanObject,
    mut v_a_316_: *mut crate::leanh::LeanObject,
    mut v_a_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: u8 = 0;
    v___x_318_ = l_Lean_Grind_nestedProofUnexpander___closed__4;
    crate::leanh::lean_inc(v_stx_315_);
    v___x_319_ = l_Lean_Syntax_isOfKind(v_stx_315_, v___x_318_);
    if v___x_319_ == 0 {
        let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_315_);
        v___x_320_ = crate::leanh::lean_box(0);
        v___x_321_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_321_, 0, v___x_320_);
        crate::leanh::lean_ctor_set(v___x_321_, 1, v_a_317_);
        return v___x_321_;
    } else {
        let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_324_: u8 = 0;
        v___x_322_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_323_ = l_Lean_Syntax_getArg(v_stx_315_, v___x_322_);
        crate::leanh::lean_dec(v_stx_315_);
        crate::leanh::lean_inc(v___x_323_);
        v___x_324_ = l_Lean_Syntax_matchesNull(v___x_323_, v___x_322_);
        if v___x_324_ == 0 {
            let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_323_);
            v___x_325_ = crate::leanh::lean_box(0);
            v___x_326_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_326_, 0, v___x_325_);
            crate::leanh::lean_ctor_set(v___x_326_, 1, v_a_317_);
            return v___x_326_;
        } else {
            let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_329_: u8 = 0;
            let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_327_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_328_ = l_Lean_Syntax_getArg(v___x_323_, v___x_327_);
            crate::leanh::lean_dec(v___x_323_);
            v___x_329_ = 0;
            v___x_330_ = l_Lean_SourceInfo_fromRef(v_a_316_, v___x_329_);
            v___x_331_ = l_Lean_Grind_nestedProofUnexpander___closed__6;
            v___x_332_ = l_Lean_Grind_nestedProofUnexpander___closed__7;
            crate::leanh::lean_inc_n(v___x_330_, 2);
            v___x_333_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_333_, 0, v___x_330_);
            crate::leanh::lean_ctor_set(v___x_333_, 1, v___x_332_);
            v___x_334_ = l_Lean_Grind_nestedProofUnexpander___closed__8;
            v___x_335_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_335_, 0, v___x_330_);
            crate::leanh::lean_ctor_set(v___x_335_, 1, v___x_334_);
            v___x_336_ =
                l_Lean_Syntax_node3(v___x_330_, v___x_331_, v___x_333_, v___x_328_, v___x_335_);
            v___x_337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_337_, 0, v___x_336_);
            crate::leanh::lean_ctor_set(v___x_337_, 1, v_a_317_);
            return v___x_337_;
        }
    }
}
pub unsafe fn l_Lean_Grind_nestedProofUnexpander___boxed(
    mut v_stx_338_: *mut crate::leanh::LeanObject,
    mut v_a_339_: *mut crate::leanh::LeanObject,
    mut v_a_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_341_ = l_Lean_Grind_nestedProofUnexpander(v_stx_338_, v_a_339_, v_a_340_);
    crate::leanh::lean_dec(v_a_339_);
    return v_res_341_;
}
pub unsafe fn l_Lean_Grind_matchCondUnexpander___redArg(
    mut v_stx_342_: *mut crate::leanh::LeanObject,
    mut v_a_343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: u8 = 0;
    v___x_344_ = l_Lean_Grind_nestedProofUnexpander___closed__4;
    crate::leanh::lean_inc(v_stx_342_);
    v___x_345_ = l_Lean_Syntax_isOfKind(v_stx_342_, v___x_344_);
    if v___x_345_ == 0 {
        let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_342_);
        v___x_346_ = crate::leanh::lean_box(0);
        v___x_347_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_347_, 0, v___x_346_);
        crate::leanh::lean_ctor_set(v___x_347_, 1, v_a_343_);
        return v___x_347_;
    } else {
        let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_350_: u8 = 0;
        v___x_348_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_349_ = l_Lean_Syntax_getArg(v_stx_342_, v___x_348_);
        crate::leanh::lean_dec(v_stx_342_);
        crate::leanh::lean_inc(v___x_349_);
        v___x_350_ = l_Lean_Syntax_matchesNull(v___x_349_, v___x_348_);
        if v___x_350_ == 0 {
            let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_349_);
            v___x_351_ = crate::leanh::lean_box(0);
            v___x_352_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_352_, 0, v___x_351_);
            crate::leanh::lean_ctor_set(v___x_352_, 1, v_a_343_);
            return v___x_352_;
        } else {
            let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_353_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_354_ = l_Lean_Syntax_getArg(v___x_349_, v___x_353_);
            crate::leanh::lean_dec(v___x_349_);
            v___x_355_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_355_, 0, v___x_354_);
            crate::leanh::lean_ctor_set(v___x_355_, 1, v_a_343_);
            return v___x_355_;
        }
    }
}
pub unsafe fn l_Lean_Grind_matchCondUnexpander(
    mut v_stx_356_: *mut crate::leanh::LeanObject,
    mut v_a_357_: *mut crate::leanh::LeanObject,
    mut v_a_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = l_Lean_Grind_matchCondUnexpander___redArg(v_stx_356_, v_a_358_);
    return v___x_359_;
}
pub unsafe fn l_Lean_Grind_matchCondUnexpander___boxed(
    mut v_stx_360_: *mut crate::leanh::LeanObject,
    mut v_a_361_: *mut crate::leanh::LeanObject,
    mut v_a_362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_363_ = l_Lean_Grind_matchCondUnexpander(v_stx_360_, v_a_361_, v_a_362_);
    crate::leanh::lean_dec(v_a_361_);
    return v_res_363_;
}
pub unsafe fn l_Lean_Grind_eqMatchUnexpander(
    mut v_stx_368_: *mut crate::leanh::LeanObject,
    mut v_a_369_: *mut crate::leanh::LeanObject,
    mut v_a_370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: u8 = 0;
    v___x_371_ = l_Lean_Grind_nestedProofUnexpander___closed__4;
    crate::leanh::lean_inc(v_stx_368_);
    v___x_372_ = l_Lean_Syntax_isOfKind(v_stx_368_, v___x_371_);
    if v___x_372_ == 0 {
        let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_368_);
        v___x_373_ = crate::leanh::lean_box(0);
        v___x_374_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_374_, 0, v___x_373_);
        crate::leanh::lean_ctor_set(v___x_374_, 1, v_a_370_);
        return v___x_374_;
    } else {
        let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_378_: u8 = 0;
        v___x_375_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_376_ = l_Lean_Syntax_getArg(v_stx_368_, v___x_375_);
        crate::leanh::lean_dec(v_stx_368_);
        v___x_377_ = crate::leanh::lean_unsigned_to_nat(2);
        crate::leanh::lean_inc(v___x_376_);
        v___x_378_ = l_Lean_Syntax_matchesNull(v___x_376_, v___x_377_);
        if v___x_378_ == 0 {
            let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_376_);
            v___x_379_ = crate::leanh::lean_box(0);
            v___x_380_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_380_, 0, v___x_379_);
            crate::leanh::lean_ctor_set(v___x_380_, 1, v_a_370_);
            return v___x_380_;
        } else {
            let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_384_: u8 = 0;
            let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_381_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_382_ = l_Lean_Syntax_getArg(v___x_376_, v___x_381_);
            v___x_383_ = l_Lean_Syntax_getArg(v___x_376_, v___x_375_);
            crate::leanh::lean_dec(v___x_376_);
            v___x_384_ = 0;
            v___x_385_ = l_Lean_SourceInfo_fromRef(v_a_369_, v___x_384_);
            v___x_386_ = l_Lean_Grind_eqMatchUnexpander___closed__1;
            v___x_387_ = l_Lean_Grind_eqMatchUnexpander___closed__2;
            crate::leanh::lean_inc(v___x_385_);
            v___x_388_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_388_, 0, v___x_385_);
            crate::leanh::lean_ctor_set(v___x_388_, 1, v___x_387_);
            v___x_389_ =
                l_Lean_Syntax_node3(v___x_385_, v___x_386_, v___x_382_, v___x_388_, v___x_383_);
            v___x_390_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_390_, 0, v___x_389_);
            crate::leanh::lean_ctor_set(v___x_390_, 1, v_a_370_);
            return v___x_390_;
        }
    }
}
pub unsafe fn l_Lean_Grind_eqMatchUnexpander___boxed(
    mut v_stx_391_: *mut crate::leanh::LeanObject,
    mut v_a_392_: *mut crate::leanh::LeanObject,
    mut v_a_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = l_Lean_Grind_eqMatchUnexpander(v_stx_391_, v_a_392_, v_a_393_);
    crate::leanh::lean_dec(v_a_392_);
    return v_res_394_;
}
pub unsafe fn l_Lean_Grind_offsetUnexpander(
    mut v_stx_399_: *mut crate::leanh::LeanObject,
    mut v_a_400_: *mut crate::leanh::LeanObject,
    mut v_a_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: u8 = 0;
    v___x_402_ = l_Lean_Grind_nestedProofUnexpander___closed__4;
    crate::leanh::lean_inc(v_stx_399_);
    v___x_403_ = l_Lean_Syntax_isOfKind(v_stx_399_, v___x_402_);
    if v___x_403_ == 0 {
        let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_399_);
        v___x_404_ = crate::leanh::lean_box(0);
        v___x_405_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_405_, 0, v___x_404_);
        crate::leanh::lean_ctor_set(v___x_405_, 1, v_a_401_);
        return v___x_405_;
    } else {
        let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_409_: u8 = 0;
        v___x_406_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_407_ = l_Lean_Syntax_getArg(v_stx_399_, v___x_406_);
        crate::leanh::lean_dec(v_stx_399_);
        v___x_408_ = crate::leanh::lean_unsigned_to_nat(2);
        crate::leanh::lean_inc(v___x_407_);
        v___x_409_ = l_Lean_Syntax_matchesNull(v___x_407_, v___x_408_);
        if v___x_409_ == 0 {
            let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_407_);
            v___x_410_ = crate::leanh::lean_box(0);
            v___x_411_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_411_, 0, v___x_410_);
            crate::leanh::lean_ctor_set(v___x_411_, 1, v_a_401_);
            return v___x_411_;
        } else {
            let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_415_: u8 = 0;
            let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_412_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_413_ = l_Lean_Syntax_getArg(v___x_407_, v___x_412_);
            v___x_414_ = l_Lean_Syntax_getArg(v___x_407_, v___x_406_);
            crate::leanh::lean_dec(v___x_407_);
            v___x_415_ = 0;
            v___x_416_ = l_Lean_SourceInfo_fromRef(v_a_400_, v___x_415_);
            v___x_417_ = l_Lean_Grind_offsetUnexpander___closed__1;
            v___x_418_ = l_Lean_Grind_offsetUnexpander___closed__2;
            crate::leanh::lean_inc(v___x_416_);
            v___x_419_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_419_, 0, v___x_416_);
            crate::leanh::lean_ctor_set(v___x_419_, 1, v___x_418_);
            v___x_420_ =
                l_Lean_Syntax_node3(v___x_416_, v___x_417_, v___x_413_, v___x_419_, v___x_414_);
            v___x_421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_421_, 0, v___x_420_);
            crate::leanh::lean_ctor_set(v___x_421_, 1, v_a_401_);
            return v___x_421_;
        }
    }
}
pub unsafe fn l_Lean_Grind_offsetUnexpander___boxed(
    mut v_stx_422_: *mut crate::leanh::LeanObject,
    mut v_a_423_: *mut crate::leanh::LeanObject,
    mut v_a_424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_425_ = l_Lean_Grind_offsetUnexpander(v_stx_422_, v_a_423_, v_a_424_);
    crate::leanh::lean_dec(v_a_423_);
    return v_res_425_;
}
pub unsafe fn l_Lean_Grind_natCastUnexpander(
    mut v_stx_430_: *mut crate::leanh::LeanObject,
    mut v_a_431_: *mut crate::leanh::LeanObject,
    mut v_a_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: u8 = 0;
    v___x_433_ = l_Lean_Grind_nestedProofUnexpander___closed__4;
    crate::leanh::lean_inc(v_stx_430_);
    v___x_434_ = l_Lean_Syntax_isOfKind(v_stx_430_, v___x_433_);
    if v___x_434_ == 0 {
        let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_430_);
        v___x_435_ = crate::leanh::lean_box(0);
        v___x_436_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_436_, 0, v___x_435_);
        crate::leanh::lean_ctor_set(v___x_436_, 1, v_a_432_);
        return v___x_436_;
    } else {
        let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_439_: u8 = 0;
        v___x_437_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_438_ = l_Lean_Syntax_getArg(v_stx_430_, v___x_437_);
        crate::leanh::lean_dec(v_stx_430_);
        crate::leanh::lean_inc(v___x_438_);
        v___x_439_ = l_Lean_Syntax_matchesNull(v___x_438_, v___x_437_);
        if v___x_439_ == 0 {
            let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_438_);
            v___x_440_ = crate::leanh::lean_box(0);
            v___x_441_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
            crate::leanh::lean_ctor_set(v___x_441_, 1, v_a_432_);
            return v___x_441_;
        } else {
            let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_444_: u8 = 0;
            let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_442_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_443_ = l_Lean_Syntax_getArg(v___x_438_, v___x_442_);
            crate::leanh::lean_dec(v___x_438_);
            v___x_444_ = 0;
            v___x_445_ = l_Lean_SourceInfo_fromRef(v_a_431_, v___x_444_);
            v___x_446_ = l_Lean_Grind_natCastUnexpander___closed__1;
            v___x_447_ = l_Lean_Grind_natCastUnexpander___closed__2;
            crate::leanh::lean_inc(v___x_445_);
            v___x_448_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_448_, 0, v___x_445_);
            crate::leanh::lean_ctor_set(v___x_448_, 1, v___x_447_);
            v___x_449_ = l_Lean_Syntax_node2(v___x_445_, v___x_446_, v___x_448_, v___x_443_);
            v___x_450_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_450_, 0, v___x_449_);
            crate::leanh::lean_ctor_set(v___x_450_, 1, v_a_432_);
            return v___x_450_;
        }
    }
}
pub unsafe fn l_Lean_Grind_natCastUnexpander___boxed(
    mut v_stx_451_: *mut crate::leanh::LeanObject,
    mut v_a_452_: *mut crate::leanh::LeanObject,
    mut v_a_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_454_ = l_Lean_Grind_natCastUnexpander(v_stx_451_, v_a_452_, v_a_453_);
    crate::leanh::lean_dec(v_a_452_);
    return v_res_454_;
}
pub unsafe fn l_Lean_Grind_Marker___redArg(
    mut v_a_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_455_);
    return v_a_455_;
}
pub unsafe fn l_Lean_Grind_Marker___redArg___boxed(
    mut v_a_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Lean_Grind_Marker___redArg(v_a_456_);
    crate::leanh::lean_dec(v_a_456_);
    return v_res_457_;
}
pub unsafe fn l_Lean_Grind_Marker(
    mut v_00_u03b1_458_: *mut crate::leanh::LeanObject,
    mut v_a_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_459_);
    return v_a_459_;
}
pub unsafe fn l_Lean_Grind_Marker___boxed(
    mut v_00_u03b1_460_: *mut crate::leanh::LeanObject,
    mut v_a_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Lean_Grind_Marker(v_00_u03b1_460_, v_a_461_);
    crate::leanh::lean_dec(v_a_461_);
    return v_res_462_;
}
pub unsafe fn _init_l_Lean_Grind_markerUnexpander___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_498_;
}
pub unsafe fn l_Lean_Grind_markerUnexpander___redArg(
    mut v_a_499_: *mut crate::leanh::LeanObject,
    mut v_a_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_501_: u8 = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_501_ = 0;
    v___x_502_ = l_Lean_SourceInfo_fromRef(v_a_499_, v___x_501_);
    v___x_503_ = l_Lean_Grind_markerUnexpander___redArg___closed__1;
    v___x_504_ = l_Lean_Grind_markerUnexpander___redArg___closed__2;
    crate::leanh::lean_inc_n(v___x_502_, 8);
    v___x_505_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_505_, 0, v___x_502_);
    crate::leanh::lean_ctor_set(v___x_505_, 1, v___x_504_);
    v___x_506_ = l_Lean_Grind_markerUnexpander___redArg___closed__5;
    v___x_507_ = l_Lean_Grind_markerUnexpander___redArg___closed__7;
    v___x_508_ = l_Lean_Grind_markerUnexpander___redArg___closed__9;
    v___x_509_ = l_Lean_Grind_markerUnexpander___redArg___closed__10;
    v___x_510_ = l_Lean_Grind_markerUnexpander___redArg___closed__11;
    v___x_511_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_511_, 0, v___x_502_);
    crate::leanh::lean_ctor_set(v___x_511_, 1, v___x_509_);
    v___x_512_ = l_Lean_Grind_markerUnexpander___redArg___closed__13;
    v___x_513_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_markerUnexpander___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Grind_markerUnexpander___redArg___closed__14_once),
        _init_l_Lean_Grind_markerUnexpander___redArg___closed__14,
    );
    v___x_514_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_514_, 0, v___x_502_);
    crate::leanh::lean_ctor_set(v___x_514_, 1, v___x_508_);
    crate::leanh::lean_ctor_set(v___x_514_, 2, v___x_513_);
    crate::leanh::lean_inc_ref_n(v___x_514_, 3);
    v___x_515_ = l_Lean_Syntax_node1(v___x_502_, v___x_512_, v___x_514_);
    v___x_516_ = l_Lean_Syntax_node5(
        v___x_502_, v___x_510_, v___x_511_, v___x_515_, v___x_514_, v___x_514_, v___x_514_,
    );
    v___x_517_ = l_Lean_Syntax_node1(v___x_502_, v___x_508_, v___x_516_);
    v___x_518_ = l_Lean_Syntax_node1(v___x_502_, v___x_507_, v___x_517_);
    v___x_519_ = l_Lean_Syntax_node1(v___x_502_, v___x_506_, v___x_518_);
    v___x_520_ = l_Lean_Syntax_node2(v___x_502_, v___x_503_, v___x_505_, v___x_519_);
    v___x_521_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_521_, 0, v___x_520_);
    crate::leanh::lean_ctor_set(v___x_521_, 1, v_a_500_);
    return v___x_521_;
}
pub unsafe fn l_Lean_Grind_markerUnexpander___redArg___boxed(
    mut v_a_522_: *mut crate::leanh::LeanObject,
    mut v_a_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Lean_Grind_markerUnexpander___redArg(v_a_522_, v_a_523_);
    crate::leanh::lean_dec(v_a_522_);
    return v_res_524_;
}
pub unsafe fn l_Lean_Grind_markerUnexpander(
    mut v_x_525_: *mut crate::leanh::LeanObject,
    mut v_a_526_: *mut crate::leanh::LeanObject,
    mut v_a_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_528_ = l_Lean_Grind_markerUnexpander___redArg(v_a_526_, v_a_527_);
    return v___x_528_;
}
pub unsafe fn l_Lean_Grind_markerUnexpander___boxed(
    mut v_x_529_: *mut crate::leanh::LeanObject,
    mut v_a_530_: *mut crate::leanh::LeanObject,
    mut v_a_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Lean_Grind_markerUnexpander(v_x_529_, v_a_530_, v_a_531_);
    crate::leanh::lean_dec(v_a_530_);
    crate::leanh::lean_dec(v_x_529_);
    return v_res_532_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Cast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Cast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Util(builtin);
}
