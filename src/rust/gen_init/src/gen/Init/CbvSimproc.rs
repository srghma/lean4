// Lean compiler output
// Module: Init.CbvSimproc
// Imports: Init.Data.ToString.Name Init.Tactics Init.Meta.Defs
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::{
    initialize_Init_Meta_Defs, l_Lean_Syntax_isNone, lean_mk_syntax_ident,
    runtime_initialize_Init_Meta_Defs,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node7,
    l_Lean_Syntax_node8,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_simpPost, l_Lean_Parser_Tactic_simpPre,
    runtime_initialize_Init_Tactics,
};
pub static l_Lean_Parser_cbvSimprocEval___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 69, 118, 97, 108, 0,
        ],
    };
static mut l_Lean_Parser_cbvSimprocEval___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Parser_cbvSimprocEval___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Parser_cbvSimprocEval___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_cbvSimprocEval___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__0_value)
                as *mut leanh::LeanObject,
            9575030279827742198 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocEval___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__4_value: leanh::LeanStringObject<9> =
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
        m_data: [99, 98, 118, 95, 101, 118, 97, 108, 0],
    };
static mut l_Lean_Parser_cbvSimprocEval___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocEval___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocEval___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocEval___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_cbvSimprocEval: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 95, 95, 67, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99,
        95, 95, 95, 95, 40, 95, 41, 58, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,7509742330559184140 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value
        ) as *mut leanh::LeanObject,
        12571085391447129896 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value
        ) as *mut leanh::LeanObject,
        18170484695678750185 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value
        ) as *mut leanh::LeanObject,
        3961966953292576997 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value) as *mut leanh::LeanObject,16084902538479694224 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__14_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__15_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 101, 108, 115, 101, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__17_value) as *mut leanh::LeanObject,393173242845875278 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__23_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 40, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__27_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__30_value) as *mut leanh::LeanObject,8609355255726335675 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 7 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__31_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__37_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value
) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 95, 67, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95,
        100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,3817038020181750064 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
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
        99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value
        ) as *mut leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 95, 66, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 95, 95, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,10086719233862156008 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 66, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 95, 40, 95, 41, 58, 61, 95, 0]};
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__0_value) as *mut leanh::LeanObject,17055111195149847261 as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 32, 0]};
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1_value) as *mut leanh::LeanObject,((( 1022 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__10_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d__:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__11_value
) as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__0_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
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
            99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_cbvSimprocPattern___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__0_value)
                as *mut leanh::LeanObject,
            5000477209128750040 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__2_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114,
            110, 37, 32, 0,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_cbvSimprocPattern___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__5_value: leanh::LeanStringObject<5> =
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
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__6_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_cbvSimprocPattern___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value) as *mut leanh::LeanObject] };
static mut l_Lean_Parser_cbvSimprocPattern___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPattern___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_cbvSimprocPattern___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__9_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_cbvSimprocPattern: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117,
        105, 108, 116, 105, 110, 0,
    ],
};
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__0_value)
            as *mut leanh::LeanObject,
        2235975067317863979 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99,
        95, 112, 97, 116, 116, 101, 114, 110, 37, 32, 0,
    ],
};
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPattern___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1_value)
            as *mut leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_cbvSimprocPatternBuiltin: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_cbvSimprocPatternBuiltin___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [65, 116, 116, 114, 0],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 65, 116, 116, 114, 0,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value)
                as *mut leanh::LeanObject,
            4584992172905639687 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__1_value)
                as *mut leanh::LeanObject,
            9353878392652886871 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocAttr___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__3_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_cbvSimprocAttr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_cbvSimprocAttr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 66, 117, 105, 108, 116, 105, 110, 65, 116,
        116, 114, 0,
    ],
};
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__0_value)
            as *mut leanh::LeanObject,
        4584992172905639687 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__0_value)
            as *mut leanh::LeanObject,
        2685779739350780851 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 0,
    ],
};
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_cbvSimprocBuiltinAttr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__6_value) as *mut leanh::LeanObject,4498178684837002829 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__11_value) as *mut leanh::LeanObject,7625897890118033792 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__12_value) as *mut leanh::LeanObject,8715860392475343861 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 105, 109, 112, 114, 111, 99, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__16_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__17_value) as *mut leanh::LeanObject,4034176598647545331 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__18_value) as *mut leanh::LeanObject,13806531830123099675 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__19_value) as *mut leanh::LeanObject,4585357269266081267 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__21_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__24_value) as *mut leanh::LeanObject,8497769072906204829 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__26_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27_value) as *mut leanh::LeanObject;
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_value) as *mut leanh::LeanObject,9063780239635860524 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 112, 97, 116, 116, 101, 114, 110, 37, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3_value) as *mut leanh::LeanObject,11509420844586769999 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6_value) as *mut leanh::LeanObject;
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_cbvSimprocEval___closed__2_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_value) as *mut leanh::LeanObject,7983999284776576032 as *mut leanh::LeanObject] };
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 95, 100, 101, 99, 108, 0]};
static mut l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_947_ = l_Lean_Parser_cbvSimprocEval;
    v___x_948_ = l_Lean_Parser_Tactic_simpPost;
    v___x_949_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18;
    v___x_950_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_950_, 0, v___x_949_);
    leanh::lean_ctor_set(v___x_950_, 1, v___x_948_);
    leanh::lean_ctor_set(v___x_950_, 2, v___x_947_);
    return v___x_950_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_951_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__19,
    );
    v___x_952_ = l_Lean_Parser_Tactic_simpPre;
    v___x_953_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__18;
    v___x_954_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_954_, 0, v___x_953_);
    leanh::lean_ctor_set(v___x_954_, 1, v___x_952_);
    leanh::lean_ctor_set(v___x_954_, 2, v___x_951_);
    return v___x_954_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__20,
    );
    v___x_956_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__5;
    v___x_957_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_957_, 0, v___x_956_);
    leanh::lean_ctor_set(v___x_957_, 1, v___x_955_);
    return v___x_957_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21,
    );
    v___x_959_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__16;
    v___x_960_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_961_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_961_, 0, v___x_960_);
    leanh::lean_ctor_set(v___x_961_, 1, v___x_959_);
    leanh::lean_ctor_set(v___x_961_, 2, v___x_958_);
    return v___x_961_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25;
    v___x_968_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__22,
    );
    v___x_969_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_970_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_970_, 0, v___x_969_);
    leanh::lean_ctor_set(v___x_970_, 1, v___x_968_);
    leanh::lean_ctor_set(v___x_970_, 2, v___x_967_);
    return v___x_970_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28;
    v___x_975_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__26,
    );
    v___x_976_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_977_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
    leanh::lean_ctor_set(v___x_977_, 1, v___x_975_);
    leanh::lean_ctor_set(v___x_977_, 2, v___x_974_);
    return v___x_977_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_984_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32;
    v___x_985_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__29,
    );
    v___x_986_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_987_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_987_, 0, v___x_986_);
    leanh::lean_ctor_set(v___x_987_, 1, v___x_985_);
    leanh::lean_ctor_set(v___x_987_, 2, v___x_984_);
    return v___x_987_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35;
    v___x_992_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__33,
    );
    v___x_993_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_994_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_994_, 0, v___x_993_);
    leanh::lean_ctor_set(v___x_994_, 1, v___x_992_);
    leanh::lean_ctor_set(v___x_994_, 2, v___x_991_);
    return v___x_994_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38;
    v___x_999_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__36,
    );
    v___x_1000_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1001_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1001_, 0, v___x_1000_);
    leanh::lean_ctor_set(v___x_1001_, 1, v___x_999_);
    leanh::lean_ctor_set(v___x_1001_, 2, v___x_998_);
    return v___x_1001_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1002_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32;
    v___x_1003_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__39,
    );
    v___x_1004_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1005_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1005_, 0, v___x_1004_);
    leanh::lean_ctor_set(v___x_1005_, 1, v___x_1003_);
    leanh::lean_ctor_set(v___x_1005_, 2, v___x_1002_);
    return v___x_1005_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1006_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__40,
    );
    v___x_1007_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1008_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1;
    v___x_1009_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1009_, 0, v___x_1008_);
    leanh::lean_ctor_set(v___x_1009_, 1, v___x_1007_);
    leanh::lean_ctor_set(v___x_1009_, 2, v___x_1006_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__()
-> *mut leanh::LeanObject {
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__41,
    );
    return v___x_1010_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21,
    );
    v___x_1065_ =
        l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__4;
    v___x_1066_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1067_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1067_, 0, v___x_1066_);
    leanh::lean_ctor_set(v___x_1067_, 1, v___x_1065_);
    leanh::lean_ctor_set(v___x_1067_, 2, v___x_1064_);
    return v___x_1067_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__25;
    v___x_1069_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__5);
    v___x_1070_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1071_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1071_, 0, v___x_1070_);
    leanh::lean_ctor_set(v___x_1071_, 1, v___x_1069_);
    leanh::lean_ctor_set(v___x_1071_, 2, v___x_1068_);
    return v___x_1071_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__28;
    v___x_1073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__6);
    v___x_1074_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1075_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1075_, 0, v___x_1074_);
    leanh::lean_ctor_set(v___x_1075_, 1, v___x_1073_);
    leanh::lean_ctor_set(v___x_1075_, 2, v___x_1072_);
    return v___x_1075_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32;
    v___x_1077_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__7);
    v___x_1078_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1079_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    leanh::lean_ctor_set(v___x_1079_, 1, v___x_1077_);
    leanh::lean_ctor_set(v___x_1079_, 2, v___x_1076_);
    return v___x_1079_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__35;
    v___x_1081_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__8);
    v___x_1082_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1083_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1083_, 0, v___x_1082_);
    leanh::lean_ctor_set(v___x_1083_, 1, v___x_1081_);
    leanh::lean_ctor_set(v___x_1083_, 2, v___x_1080_);
    return v___x_1083_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1084_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__38;
    v___x_1085_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__9);
    v___x_1086_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1087_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1087_, 0, v___x_1086_);
    leanh::lean_ctor_set(v___x_1087_, 1, v___x_1085_);
    leanh::lean_ctor_set(v___x_1087_, 2, v___x_1084_);
    return v___x_1087_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1088_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__32;
    v___x_1089_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__10);
    v___x_1090_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1091_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1091_, 0, v___x_1090_);
    leanh::lean_ctor_set(v___x_1091_, 1, v___x_1089_);
    leanh::lean_ctor_set(v___x_1091_, 2, v___x_1088_);
    return v___x_1091_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__11);
    v___x_1093_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1094_ =
        l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1;
    v___x_1095_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    leanh::lean_ctor_set(v___x_1095_, 1, v___x_1093_);
    leanh::lean_ctor_set(v___x_1095_, 2, v___x_1092_);
    return v___x_1095_;
}
pub unsafe fn _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__()
-> *mut leanh::LeanObject {
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1096_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12), core::ptr::addr_of_mut!(l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12_once), _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__12);
    return v___x_1096_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21,
    );
    v___x_1203_ = l_Lean_Parser_Attr_cbvSimprocAttr___closed__4;
    v___x_1204_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1205_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1205_, 0, v___x_1204_);
    leanh::lean_ctor_set(v___x_1205_, 1, v___x_1203_);
    leanh::lean_ctor_set(v___x_1205_, 2, v___x_1202_);
    return v___x_1205_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__5,
    );
    v___x_1207_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1208_ = l_Lean_Parser_Attr_cbvSimprocAttr___closed__2;
    v___x_1209_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1209_, 0, v___x_1208_);
    leanh::lean_ctor_set(v___x_1209_, 1, v___x_1207_);
    leanh::lean_ctor_set(v___x_1209_, 2, v___x_1206_);
    return v___x_1209_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocAttr() -> *mut leanh::LeanObject {
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocAttr___closed__6_once),
        _init_l_Lean_Parser_Attr_cbvSimprocAttr___closed__6,
    );
    return v___x_1210_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21_once
        ),
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__21,
    );
    v___x_1222_ = l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__3;
    v___x_1223_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__3;
    v___x_1224_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1224_, 0, v___x_1223_);
    leanh::lean_ctor_set(v___x_1224_, 1, v___x_1222_);
    leanh::lean_ctor_set(v___x_1224_, 2, v___x_1221_);
    return v___x_1224_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4_once),
        _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__4,
    );
    v___x_1226_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1227_ = l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1;
    v___x_1228_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1228_, 0, v___x_1227_);
    leanh::lean_ctor_set(v___x_1228_, 1, v___x_1226_);
    leanh::lean_ctor_set(v___x_1228_, 2, v___x_1225_);
    return v___x_1228_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr() -> *mut leanh::LeanObject {
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5_once),
        _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__5,
    );
    return v___x_1229_;
}
pub unsafe fn _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1280_;
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: u8 = 0;
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocType_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1291_ = l_Lean_Parser_cbvSimprocEval___closed__1;
                v___x_1292_ = l_Lean_Parser_cbvSimprocEval___closed__2;
                v___x_1374_ =
                    l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_1288_);
                v___x_1375_ = l_Lean_Syntax_isOfKind(v_x_1288_, v___x_1374_);
                if v___x_1375_ == 0 {
                    leanh::lean_dec(v_x_1288_);
                    v___x_1376_ = leanh::lean_box(1);
                    v___x_1377_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1377_, 0, v___x_1376_);
                    leanh::lean_ctor_set(v___x_1377_, 1, v_a_1290_);
                    return v___x_1377_;
                } else {
                    v___x_1378_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1379_ = l_Lean_Syntax_getArg(v_x_1288_, v___x_1378_);
                    v___x_1380_ = l_Lean_Syntax_isNone(v___x_1379_);
                    if v___x_1380_ == 0 {
                        v___x_1381_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1379_);
                        v___x_1382_ = l_Lean_Syntax_matchesNull(v___x_1379_, v___x_1381_);
                        if v___x_1382_ == 0 {
                            leanh::lean_dec(v___x_1379_);
                            leanh::lean_dec(v_x_1288_);
                            v___x_1383_ = leanh::lean_box(1);
                            v___x_1384_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1384_, 0, v___x_1383_);
                            leanh::lean_ctor_set(v___x_1384_, 1, v_a_1290_);
                            return v___x_1384_;
                        } else {
                            v_doc_x3f_1385_ = l_Lean_Syntax_getArg(v___x_1379_, v___x_1378_);
                            leanh::lean_dec(v___x_1379_);
                            v___x_1386_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30;
                            leanh::lean_inc(v_doc_x3f_1385_);
                            v___x_1387_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1385_, v___x_1386_);
                            if v___x_1387_ == 0 {
                                leanh::lean_dec(v_doc_x3f_1385_);
                                leanh::lean_dec(v_x_1288_);
                                v___x_1388_ = leanh::lean_box(1);
                                v___x_1389_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1389_, 0, v___x_1388_);
                                leanh::lean_ctor_set(v___x_1389_, 1, v_a_1290_);
                                return v___x_1389_;
                            } else {
                                v___x_1390_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1390_, 0, v_doc_x3f_1385_);
                                v_doc_x3f_1349_ = v___x_1390_;
                                v___y_1350_ = v_a_1289_;
                                v___y_1351_ = v_a_1290_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1379_);
                        v___x_1391_ = leanh::lean_box(0);
                        v_doc_x3f_1349_ = v___x_1391_;
                        v___y_1350_ = v_a_1289_;
                        v___y_1351_ = v_a_1290_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_1300_, 2);
                v___x_1306_ = l_Array_append___redArg(v___y_1300_, v___y_1305_);
                leanh::lean_dec_ref(v___y_1305_);
                leanh::lean_inc_n(v___y_1296_, 5);
                leanh::lean_inc_n(v___y_1297_, 20);
                v___x_1307_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1307_, 0, v___y_1297_);
                leanh::lean_ctor_set(v___x_1307_, 1, v___y_1296_);
                leanh::lean_ctor_set(v___x_1307_, 2, v___x_1306_);
                v___x_1308_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1308_, 0, v___y_1297_);
                leanh::lean_ctor_set(v___x_1308_, 1, v___y_1296_);
                leanh::lean_ctor_set(v___x_1308_, 2, v___y_1300_);
                v___x_1309_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                leanh::lean_inc_ref_n(v___y_1304_, 5);
                v___x_1310_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1309_);
                v___x_1311_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1311_, 0, v___y_1297_);
                leanh::lean_ctor_set(v___x_1311_, 1, v___x_1309_);
                v___x_1312_ = l_Lean_Syntax_node1(v___y_1297_, v___x_1310_, v___x_1311_);
                v___x_1313_ = l_Lean_Syntax_node1(v___y_1297_, v___y_1296_, v___x_1312_);
                leanh::lean_inc_ref_n(v___x_1308_, 10);
                leanh::lean_inc(v___y_1295_);
                v___x_1314_ = l_Lean_Syntax_node7(
                    v___y_1297_,
                    v___y_1295_,
                    v___x_1307_,
                    v___x_1308_,
                    v___x_1308_,
                    v___x_1308_,
                    v___x_1313_,
                    v___x_1308_,
                    v___x_1308_,
                );
                v___x_1315_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1;
                v___x_1316_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1315_);
                v___x_1317_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_1318_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1318_, 0, v___y_1297_);
                leanh::lean_ctor_set(v___x_1318_, 1, v___x_1317_);
                v___x_1319_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_1320_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1319_);
                leanh::lean_inc(v___y_1299_);
                v___x_1321_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___x_1320_, v___y_1299_, v___x_1308_);
                v___x_1322_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_1323_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1322_);
                v___x_1324_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_1325_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_1326_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1326_, 0, v___y_1297_);
                leanh::lean_ctor_set(v___x_1326_, 1, v___x_1325_);
                leanh::lean_inc(v___y_1294_);
                v___x_1327_ = lean_mk_syntax_ident(v___y_1294_);
                v___x_1328_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___x_1324_, v___x_1326_, v___x_1327_);
                v___x_1329_ = l_Lean_Syntax_node1(v___y_1297_, v___y_1296_, v___x_1328_);
                v___x_1330_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___x_1323_, v___x_1308_, v___x_1329_);
                v___x_1331_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9;
                v___x_1332_ =
                    l_Lean_Name_mkStr4(v___x_1291_, v___x_1292_, v___y_1304_, v___x_1331_);
                v___x_1333_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_1334_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1334_, 0, v___y_1297_);
                leanh::lean_ctor_set(v___x_1334_, 1, v___x_1333_);
                v___x_1335_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13;
                v___x_1336_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___x_1335_, v___x_1308_, v___x_1308_);
                v___x_1337_ = l_Lean_Syntax_node4(
                    v___y_1297_,
                    v___x_1332_,
                    v___x_1334_,
                    v___y_1302_,
                    v___x_1336_,
                    v___x_1308_,
                );
                v___x_1338_ = l_Lean_Syntax_node5(
                    v___y_1297_,
                    v___x_1316_,
                    v___x_1318_,
                    v___x_1321_,
                    v___x_1330_,
                    v___x_1337_,
                    v___x_1308_,
                );
                leanh::lean_inc(v___y_1303_);
                v___x_1339_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___y_1303_, v___x_1314_, v___x_1338_);
                v___x_1340_ = l_Lean_Parser_cbvSimprocPattern___closed__1;
                v___x_1341_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__14;
                v___x_1342_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1342_, 0, v___y_1297_);
                leanh::lean_ctor_set(v___x_1342_, 1, v___x_1341_);
                v___x_1343_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_1344_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1344_, 0, v___y_1297_);
                leanh::lean_ctor_set(v___x_1344_, 1, v___x_1343_);
                v___x_1345_ = l_Lean_Syntax_node4(
                    v___y_1297_,
                    v___x_1340_,
                    v___x_1342_,
                    v___y_1298_,
                    v___x_1344_,
                    v___y_1299_,
                );
                v___x_1346_ =
                    l_Lean_Syntax_node2(v___y_1297_, v___y_1296_, v___x_1339_, v___x_1345_);
                v___x_1347_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1347_, 0, v___x_1346_);
                leanh::lean_ctor_set(v___x_1347_, 1, v___y_1301_);
                return v___x_1347_;
            }
            2 => {
                v___x_1352_ = leanh::lean_unsigned_to_nat(2);
                v___x_1353_ = l_Lean_Syntax_getArg(v_x_1288_, v___x_1352_);
                v___x_1354_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24;
                leanh::lean_inc(v___x_1353_);
                v___x_1355_ = l_Lean_Syntax_isOfKind(v___x_1353_, v___x_1354_);
                if v___x_1355_ == 0 {
                    leanh::lean_dec(v___x_1353_);
                    leanh::lean_dec(v_doc_x3f_1349_);
                    leanh::lean_dec(v_x_1288_);
                    v___x_1356_ = leanh::lean_box(1);
                    v___x_1357_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                    leanh::lean_ctor_set(v___x_1357_, 1, v___y_1351_);
                    return v___x_1357_;
                } else {
                    v_ref_1358_ = leanh::lean_ctor_get(v___y_1350_, 5);
                    v___x_1359_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1360_ = l_Lean_Syntax_getArg(v_x_1288_, v___x_1359_);
                    v___x_1361_ = leanh::lean_unsigned_to_nat(7);
                    v___x_1362_ = l_Lean_Syntax_getArg(v_x_1288_, v___x_1361_);
                    leanh::lean_dec(v_x_1288_);
                    v_simprocType_1363_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20;
                    v___x_1364_ = 0;
                    v___x_1365_ = l_Lean_SourceInfo_fromRef(v_ref_1358_, v___x_1364_);
                    v___x_1366_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_1367_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23;
                    v___x_1368_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25;
                    v___x_1369_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27;
                    v___x_1370_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once), _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
                    if leanh::lean_obj_tag(v_doc_x3f_1349_) == 1 {
                        v_val_1371_ = leanh::lean_ctor_get(v_doc_x3f_1349_, 0);
                        leanh::lean_inc(v_val_1371_);
                        leanh::lean_dec_ref_known(v_doc_x3f_1349_, 1);
                        v___x_1372_ = l_Array_mkArray1___redArg(v_val_1371_);
                        v___y_1294_ = v_simprocType_1363_;
                        v___y_1295_ = v___x_1369_;
                        v___y_1296_ = v___x_1366_;
                        v___y_1297_ = v___x_1365_;
                        v___y_1298_ = v___x_1360_;
                        v___y_1299_ = v___x_1353_;
                        v___y_1300_ = v___x_1370_;
                        v___y_1301_ = v___y_1351_;
                        v___y_1302_ = v___x_1362_;
                        v___y_1303_ = v___x_1368_;
                        v___y_1304_ = v___x_1367_;
                        v___y_1305_ = v___x_1372_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_doc_x3f_1349_);
                        v___x_1373_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                        v___y_1294_ = v_simprocType_1363_;
                        v___y_1295_ = v___x_1369_;
                        v___y_1296_ = v___x_1366_;
                        v___y_1297_ = v___x_1365_;
                        v___y_1298_ = v___x_1360_;
                        v___y_1299_ = v___x_1353_;
                        v___y_1300_ = v___x_1370_;
                        v___y_1301_ = v___y_1351_;
                        v___y_1302_ = v___x_1362_;
                        v___y_1303_ = v___x_1368_;
                        v___y_1304_ = v___x_1367_;
                        v___y_1305_ = v___x_1373_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(
    mut v_x_1392_: *mut leanh::LeanObject,
    mut v_a_1393_: *mut leanh::LeanObject,
    mut v_a_1394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1395_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1(v_x_1392_, v_a_1393_, v_a_1394_);
    leanh::lean_dec_ref(v_a_1393_);
    return v_res_1395_;
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(
    mut v_x_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocType_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: u8 = 0;
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: u8 = 0;
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = l_Lean_Parser_cbvSimprocEval___closed__1;
                v___x_1401_ = l_Lean_Parser_cbvSimprocEval___closed__2;
                v___x_1478_ = l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_1397_);
                v___x_1479_ = l_Lean_Syntax_isOfKind(v_x_1397_, v___x_1478_);
                if v___x_1479_ == 0 {
                    leanh::lean_dec(v_x_1397_);
                    v___x_1480_ = leanh::lean_box(1);
                    v___x_1481_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1481_, 0, v___x_1480_);
                    leanh::lean_ctor_set(v___x_1481_, 1, v_a_1399_);
                    return v___x_1481_;
                } else {
                    v___x_1482_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1483_ = l_Lean_Syntax_getArg(v_x_1397_, v___x_1482_);
                    v___x_1484_ = l_Lean_Syntax_isNone(v___x_1483_);
                    if v___x_1484_ == 0 {
                        v___x_1485_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1483_);
                        v___x_1486_ = l_Lean_Syntax_matchesNull(v___x_1483_, v___x_1485_);
                        if v___x_1486_ == 0 {
                            leanh::lean_dec(v___x_1483_);
                            leanh::lean_dec(v_x_1397_);
                            v___x_1487_ = leanh::lean_box(1);
                            v___x_1488_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1488_, 0, v___x_1487_);
                            leanh::lean_ctor_set(v___x_1488_, 1, v_a_1399_);
                            return v___x_1488_;
                        } else {
                            v_doc_x3f_1489_ = l_Lean_Syntax_getArg(v___x_1483_, v___x_1482_);
                            leanh::lean_dec(v___x_1483_);
                            v___x_1490_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30;
                            leanh::lean_inc(v_doc_x3f_1489_);
                            v___x_1491_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1489_, v___x_1490_);
                            if v___x_1491_ == 0 {
                                leanh::lean_dec(v_doc_x3f_1489_);
                                leanh::lean_dec(v_x_1397_);
                                v___x_1492_ = leanh::lean_box(1);
                                v___x_1493_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1493_, 0, v___x_1492_);
                                leanh::lean_ctor_set(v___x_1493_, 1, v_a_1399_);
                                return v___x_1493_;
                            } else {
                                v___x_1494_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1494_, 0, v_doc_x3f_1489_);
                                v_doc_x3f_1453_ = v___x_1494_;
                                v___y_1454_ = v_a_1398_;
                                v___y_1455_ = v_a_1399_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1483_);
                        v___x_1495_ = leanh::lean_box(0);
                        v_doc_x3f_1453_ = v___x_1495_;
                        v___y_1454_ = v_a_1398_;
                        v___y_1455_ = v_a_1399_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_1405_, 2);
                v___x_1415_ = l_Array_append___redArg(v___y_1405_, v___y_1414_);
                leanh::lean_dec_ref(v___y_1414_);
                leanh::lean_inc_n(v___y_1413_, 4);
                leanh::lean_inc_n(v___y_1404_, 17);
                v___x_1416_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1416_, 0, v___y_1404_);
                leanh::lean_ctor_set(v___x_1416_, 1, v___y_1413_);
                leanh::lean_ctor_set(v___x_1416_, 2, v___x_1415_);
                v___x_1417_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1417_, 0, v___y_1404_);
                leanh::lean_ctor_set(v___x_1417_, 1, v___y_1413_);
                leanh::lean_ctor_set(v___x_1417_, 2, v___y_1405_);
                leanh::lean_inc_ref_n(v___x_1417_, 11);
                leanh::lean_inc(v___y_1412_);
                v___x_1418_ = l_Lean_Syntax_node7(
                    v___y_1404_,
                    v___y_1412_,
                    v___x_1416_,
                    v___x_1417_,
                    v___x_1417_,
                    v___x_1417_,
                    v___x_1417_,
                    v___x_1417_,
                    v___x_1417_,
                );
                v___x_1419_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__1;
                leanh::lean_inc_ref_n(v___y_1406_, 4);
                v___x_1420_ =
                    l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___y_1406_, v___x_1419_);
                v___x_1421_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__2;
                v___x_1422_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1422_, 0, v___y_1404_);
                leanh::lean_ctor_set(v___x_1422_, 1, v___x_1421_);
                v___x_1423_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__3;
                v___x_1424_ =
                    l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___y_1406_, v___x_1423_);
                leanh::lean_inc(v___y_1411_);
                v___x_1425_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___x_1424_, v___y_1411_, v___x_1417_);
                v___x_1426_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__4;
                v___x_1427_ =
                    l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___y_1406_, v___x_1426_);
                v___x_1428_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__7;
                v___x_1429_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__8;
                v___x_1430_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1430_, 0, v___y_1404_);
                leanh::lean_ctor_set(v___x_1430_, 1, v___x_1429_);
                leanh::lean_inc(v___y_1403_);
                v___x_1431_ = lean_mk_syntax_ident(v___y_1403_);
                v___x_1432_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___x_1428_, v___x_1430_, v___x_1431_);
                v___x_1433_ = l_Lean_Syntax_node1(v___y_1404_, v___y_1413_, v___x_1432_);
                v___x_1434_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___x_1427_, v___x_1417_, v___x_1433_);
                v___x_1435_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__9;
                v___x_1436_ =
                    l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___y_1406_, v___x_1435_);
                v___x_1437_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_1438_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1438_, 0, v___y_1404_);
                leanh::lean_ctor_set(v___x_1438_, 1, v___x_1437_);
                v___x_1439_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__13;
                v___x_1440_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___x_1439_, v___x_1417_, v___x_1417_);
                v___x_1441_ = l_Lean_Syntax_node4(
                    v___y_1404_,
                    v___x_1436_,
                    v___x_1438_,
                    v___y_1408_,
                    v___x_1440_,
                    v___x_1417_,
                );
                v___x_1442_ = l_Lean_Syntax_node5(
                    v___y_1404_,
                    v___x_1420_,
                    v___x_1422_,
                    v___x_1425_,
                    v___x_1434_,
                    v___x_1441_,
                    v___x_1417_,
                );
                leanh::lean_inc(v___y_1410_);
                v___x_1443_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___y_1410_, v___x_1418_, v___x_1442_);
                v___x_1444_ = l_Lean_Parser_cbvSimprocPatternBuiltin___closed__1;
                v___x_1445_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__0;
                v___x_1446_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1446_, 0, v___y_1404_);
                leanh::lean_ctor_set(v___x_1446_, 1, v___x_1445_);
                v___x_1447_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__15;
                v___x_1448_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1448_, 0, v___y_1404_);
                leanh::lean_ctor_set(v___x_1448_, 1, v___x_1447_);
                v___x_1449_ = l_Lean_Syntax_node4(
                    v___y_1404_,
                    v___x_1444_,
                    v___x_1446_,
                    v___y_1409_,
                    v___x_1448_,
                    v___y_1411_,
                );
                v___x_1450_ =
                    l_Lean_Syntax_node2(v___y_1404_, v___y_1413_, v___x_1443_, v___x_1449_);
                v___x_1451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
                leanh::lean_ctor_set(v___x_1451_, 1, v___y_1407_);
                return v___x_1451_;
            }
            2 => {
                v___x_1456_ = leanh::lean_unsigned_to_nat(2);
                v___x_1457_ = l_Lean_Syntax_getArg(v_x_1397_, v___x_1456_);
                v___x_1458_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24;
                leanh::lean_inc(v___x_1457_);
                v___x_1459_ = l_Lean_Syntax_isOfKind(v___x_1457_, v___x_1458_);
                if v___x_1459_ == 0 {
                    leanh::lean_dec(v___x_1457_);
                    leanh::lean_dec(v_doc_x3f_1453_);
                    leanh::lean_dec(v_x_1397_);
                    v___x_1460_ = leanh::lean_box(1);
                    v___x_1461_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1461_, 0, v___x_1460_);
                    leanh::lean_ctor_set(v___x_1461_, 1, v___y_1455_);
                    return v___x_1461_;
                } else {
                    v_ref_1462_ = leanh::lean_ctor_get(v___y_1454_, 5);
                    v___x_1463_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1464_ = l_Lean_Syntax_getArg(v_x_1397_, v___x_1463_);
                    v___x_1465_ = leanh::lean_unsigned_to_nat(7);
                    v___x_1466_ = l_Lean_Syntax_getArg(v_x_1397_, v___x_1465_);
                    leanh::lean_dec(v_x_1397_);
                    v_simprocType_1467_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__20;
                    v___x_1468_ = 0;
                    v___x_1469_ = l_Lean_SourceInfo_fromRef(v_ref_1462_, v___x_1468_);
                    v___x_1470_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_1471_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__23;
                    v___x_1472_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__25;
                    v___x_1473_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__27;
                    v___x_1474_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once), _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
                    if leanh::lean_obj_tag(v_doc_x3f_1453_) == 1 {
                        v_val_1475_ = leanh::lean_ctor_get(v_doc_x3f_1453_, 0);
                        leanh::lean_inc(v_val_1475_);
                        leanh::lean_dec_ref_known(v_doc_x3f_1453_, 1);
                        v___x_1476_ = l_Array_mkArray1___redArg(v_val_1475_);
                        v___y_1403_ = v_simprocType_1467_;
                        v___y_1404_ = v___x_1469_;
                        v___y_1405_ = v___x_1474_;
                        v___y_1406_ = v___x_1471_;
                        v___y_1407_ = v___y_1455_;
                        v___y_1408_ = v___x_1466_;
                        v___y_1409_ = v___x_1464_;
                        v___y_1410_ = v___x_1472_;
                        v___y_1411_ = v___x_1457_;
                        v___y_1412_ = v___x_1473_;
                        v___y_1413_ = v___x_1470_;
                        v___y_1414_ = v___x_1476_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_doc_x3f_1453_);
                        v___x_1477_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                        v___y_1403_ = v_simprocType_1467_;
                        v___y_1404_ = v___x_1469_;
                        v___y_1405_ = v___x_1474_;
                        v___y_1406_ = v___x_1471_;
                        v___y_1407_ = v___y_1455_;
                        v___y_1408_ = v___x_1466_;
                        v___y_1409_ = v___x_1464_;
                        v___y_1410_ = v___x_1472_;
                        v___y_1411_ = v___x_1457_;
                        v___y_1412_ = v___x_1473_;
                        v___y_1413_ = v___x_1470_;
                        v___y_1414_ = v___x_1477_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1___boxed(
    mut v_x_1496_: *mut leanh::LeanObject,
    mut v_a_1497_: *mut leanh::LeanObject,
    mut v_a_1498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d____1(v_x_1496_, v_a_1497_, v_a_1498_);
    leanh::lean_dec_ref(v_a_1497_);
    return v_res_1499_;
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(
    mut v_x_1516_: *mut leanh::LeanObject,
    mut v_a_1517_: *mut leanh::LeanObject,
    mut v_a_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_phase_x3f_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_phase_x3f_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1545_ = l_Lean_Parser_cbvSimprocEval___closed__1;
                v___x_1546_ = l_Lean_Parser_cbvSimprocEval___closed__2;
                v___x_1547_ =
                    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_1516_);
                v___x_1548_ = l_Lean_Syntax_isOfKind(v_x_1516_, v___x_1547_);
                if v___x_1548_ == 0 {
                    leanh::lean_dec(v_x_1516_);
                    v___x_1549_ = leanh::lean_box(1);
                    v___x_1550_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1550_, 0, v___x_1549_);
                    leanh::lean_ctor_set(v___x_1550_, 1, v_a_1518_);
                    return v___x_1550_;
                } else {
                    v___x_1551_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1634_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1551_);
                    v___x_1635_ = l_Lean_Syntax_isNone(v___x_1634_);
                    if v___x_1635_ == 0 {
                        v___x_1636_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1634_);
                        v___x_1637_ = l_Lean_Syntax_matchesNull(v___x_1634_, v___x_1636_);
                        if v___x_1637_ == 0 {
                            leanh::lean_dec(v___x_1634_);
                            leanh::lean_dec(v_x_1516_);
                            v___x_1638_ = leanh::lean_box(1);
                            v___x_1639_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1639_, 0, v___x_1638_);
                            leanh::lean_ctor_set(v___x_1639_, 1, v_a_1518_);
                            return v___x_1639_;
                        } else {
                            v_doc_x3f_1640_ = l_Lean_Syntax_getArg(v___x_1634_, v___x_1551_);
                            leanh::lean_dec(v___x_1634_);
                            v___x_1641_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30;
                            leanh::lean_inc(v_doc_x3f_1640_);
                            v___x_1642_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1640_, v___x_1641_);
                            if v___x_1642_ == 0 {
                                leanh::lean_dec(v_doc_x3f_1640_);
                                leanh::lean_dec(v_x_1516_);
                                v___x_1643_ = leanh::lean_box(1);
                                v___x_1644_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1644_, 0, v___x_1643_);
                                leanh::lean_ctor_set(v___x_1644_, 1, v_a_1518_);
                                return v___x_1644_;
                            } else {
                                v___x_1645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1645_, 0, v_doc_x3f_1640_);
                                v_doc_x3f_1616_ = v___x_1645_;
                                v___y_1617_ = v_a_1517_;
                                v___y_1618_ = v_a_1518_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1634_);
                        v___x_1646_ = leanh::lean_box(0);
                        v_doc_x3f_1616_ = v___x_1646_;
                        v___y_1617_ = v_a_1517_;
                        v___y_1618_ = v_a_1518_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_1524_);
                v___x_1534_ = l_Array_append___redArg(v___y_1524_, v___y_1533_);
                leanh::lean_dec_ref(v___y_1533_);
                leanh::lean_inc_n(v___y_1531_, 4);
                leanh::lean_inc_n(v___y_1522_, 7);
                v___x_1535_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1535_, 0, v___y_1522_);
                leanh::lean_ctor_set(v___x_1535_, 1, v___y_1531_);
                leanh::lean_ctor_set(v___x_1535_, 2, v___x_1534_);
                leanh::lean_inc(v___y_1529_);
                v___x_1536_ =
                    l_Lean_Syntax_node2(v___y_1522_, v___y_1529_, v___y_1525_, v___x_1535_);
                v___x_1537_ =
                    l_Lean_Syntax_node2(v___y_1522_, v___y_1521_, v___y_1530_, v___x_1536_);
                v___x_1538_ = l_Lean_Syntax_node1(v___y_1522_, v___y_1531_, v___x_1537_);
                v___x_1539_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0;
                v___x_1540_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1540_, 0, v___y_1522_);
                leanh::lean_ctor_set(v___x_1540_, 1, v___x_1539_);
                v___x_1541_ = l_Lean_Syntax_node1(v___y_1522_, v___y_1531_, v___y_1523_);
                leanh::lean_inc(v___y_1526_);
                v___x_1542_ = l_Lean_Syntax_node5(
                    v___y_1522_,
                    v___y_1526_,
                    v___y_1532_,
                    v___y_1527_,
                    v___x_1538_,
                    v___x_1540_,
                    v___x_1541_,
                );
                v___x_1543_ =
                    l_Lean_Syntax_node2(v___y_1522_, v___y_1531_, v___y_1520_, v___x_1542_);
                v___x_1544_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1544_, 0, v___x_1543_);
                leanh::lean_ctor_set(v___x_1544_, 1, v___y_1528_);
                return v___x_1544_;
            }
            2 => {
                leanh::lean_inc_ref(v___y_1561_);
                v___x_1565_ = l_Array_append___redArg(v___y_1561_, v___y_1564_);
                leanh::lean_dec_ref(v___y_1564_);
                leanh::lean_inc(v___y_1559_);
                leanh::lean_inc_n(v___y_1556_, 9);
                v___x_1566_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1566_, 0, v___y_1556_);
                leanh::lean_ctor_set(v___x_1566_, 1, v___y_1559_);
                leanh::lean_ctor_set(v___x_1566_, 2, v___x_1565_);
                v___x_1567_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__1;
                v___x_1568_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1568_, 0, v___y_1556_);
                leanh::lean_ctor_set(v___x_1568_, 1, v___x_1567_);
                v___x_1569_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2;
                v___x_1570_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1570_, 0, v___y_1556_);
                leanh::lean_ctor_set(v___x_1570_, 1, v___x_1569_);
                v___x_1571_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34;
                v___x_1572_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1572_, 0, v___y_1556_);
                leanh::lean_ctor_set(v___x_1572_, 1, v___x_1571_);
                v___x_1573_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_1574_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1574_, 0, v___y_1556_);
                leanh::lean_ctor_set(v___x_1574_, 1, v___x_1573_);
                leanh::lean_inc(v___y_1558_);
                leanh::lean_inc(v___y_1563_);
                v___x_1575_ = l_Lean_Syntax_node8(
                    v___y_1556_,
                    v___y_1563_,
                    v___x_1566_,
                    v___x_1568_,
                    v___y_1558_,
                    v___x_1570_,
                    v___y_1560_,
                    v___x_1572_,
                    v___x_1574_,
                    v___y_1553_,
                );
                v___x_1576_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3;
                v___x_1577_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4;
                v___x_1578_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1578_, 0, v___y_1556_);
                leanh::lean_ctor_set(v___x_1578_, 1, v___x_1576_);
                v___x_1579_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5;
                v___x_1580_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1580_, 0, v___y_1556_);
                leanh::lean_ctor_set(v___x_1580_, 1, v___x_1579_);
                v___x_1581_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6;
                leanh::lean_inc_ref(v___y_1562_);
                v___x_1582_ =
                    l_Lean_Name_mkStr4(v___x_1545_, v___x_1546_, v___y_1562_, v___x_1581_);
                v___x_1583_ = l_Lean_Parser_Attr_cbvSimprocAttr___closed__2;
                v___x_1584_ = l_Lean_Parser_Attr_cbvSimprocAttr___closed__3;
                v___x_1585_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1585_, 0, v___y_1556_);
                leanh::lean_ctor_set(v___x_1585_, 1, v___x_1584_);
                if leanh::lean_obj_tag(v___y_1557_) == 1 {
                    v_val_1586_ = leanh::lean_ctor_get(v___y_1557_, 0);
                    leanh::lean_inc(v_val_1586_);
                    leanh::lean_dec_ref_known(v___y_1557_, 1);
                    v___x_1587_ = l_Array_mkArray1___redArg(v_val_1586_);
                    v___y_1520_ = v___x_1575_;
                    v___y_1521_ = v___x_1582_;
                    v___y_1522_ = v___y_1556_;
                    v___y_1523_ = v___y_1558_;
                    v___y_1524_ = v___y_1561_;
                    v___y_1525_ = v___x_1585_;
                    v___y_1526_ = v___x_1577_;
                    v___y_1527_ = v___x_1580_;
                    v___y_1528_ = v___y_1554_;
                    v___y_1529_ = v___x_1583_;
                    v___y_1530_ = v___y_1555_;
                    v___y_1531_ = v___y_1559_;
                    v___y_1532_ = v___x_1578_;
                    v___y_1533_ = v___x_1587_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1557_);
                    v___x_1588_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                    v___y_1520_ = v___x_1575_;
                    v___y_1521_ = v___x_1582_;
                    v___y_1522_ = v___y_1556_;
                    v___y_1523_ = v___y_1558_;
                    v___y_1524_ = v___y_1561_;
                    v___y_1525_ = v___x_1585_;
                    v___y_1526_ = v___x_1577_;
                    v___y_1527_ = v___x_1580_;
                    v___y_1528_ = v___y_1554_;
                    v___y_1529_ = v___x_1583_;
                    v___y_1530_ = v___y_1555_;
                    v___y_1531_ = v___y_1559_;
                    v___y_1532_ = v___x_1578_;
                    v___y_1533_ = v___x_1588_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1595_ = leanh::lean_unsigned_to_nat(4);
                v___x_1596_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1595_);
                v___x_1597_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24;
                leanh::lean_inc(v___x_1596_);
                v___x_1598_ = l_Lean_Syntax_isOfKind(v___x_1596_, v___x_1597_);
                if v___x_1598_ == 0 {
                    leanh::lean_dec(v___x_1596_);
                    leanh::lean_dec(v_phase_x3f_1592_);
                    leanh::lean_dec(v___y_1591_);
                    leanh::lean_dec(v___y_1590_);
                    leanh::lean_dec(v_x_1516_);
                    v___x_1599_ = leanh::lean_box(1);
                    v___x_1600_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1600_, 0, v___x_1599_);
                    leanh::lean_ctor_set(v___x_1600_, 1, v___y_1594_);
                    return v___x_1600_;
                } else {
                    v_ref_1601_ = leanh::lean_ctor_get(v___y_1593_, 5);
                    v___x_1602_ = leanh::lean_unsigned_to_nat(6);
                    v___x_1603_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1602_);
                    v___x_1604_ = leanh::lean_unsigned_to_nat(9);
                    v___x_1605_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1604_);
                    leanh::lean_dec(v_x_1516_);
                    v___x_1606_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5;
                    v___x_1607_ = 0;
                    v___x_1608_ = l_Lean_SourceInfo_fromRef(v_ref_1601_, v___x_1607_);
                    v___x_1609_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_1610_ = l_Lean_Parser_command__Cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                    v___x_1611_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once), _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
                    if leanh::lean_obj_tag(v___y_1591_) == 1 {
                        v_val_1612_ = leanh::lean_ctor_get(v___y_1591_, 0);
                        leanh::lean_inc(v_val_1612_);
                        leanh::lean_dec_ref_known(v___y_1591_, 1);
                        v___x_1613_ = l_Array_mkArray1___redArg(v_val_1612_);
                        v___y_1553_ = v___x_1605_;
                        v___y_1554_ = v___y_1594_;
                        v___y_1555_ = v___y_1590_;
                        v___y_1556_ = v___x_1608_;
                        v___y_1557_ = v_phase_x3f_1592_;
                        v___y_1558_ = v___x_1596_;
                        v___y_1559_ = v___x_1609_;
                        v___y_1560_ = v___x_1603_;
                        v___y_1561_ = v___x_1611_;
                        v___y_1562_ = v___x_1606_;
                        v___y_1563_ = v___x_1610_;
                        v___y_1564_ = v___x_1613_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1591_);
                        v___x_1614_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                        v___y_1553_ = v___x_1605_;
                        v___y_1554_ = v___y_1594_;
                        v___y_1555_ = v___y_1590_;
                        v___y_1556_ = v___x_1608_;
                        v___y_1557_ = v_phase_x3f_1592_;
                        v___y_1558_ = v___x_1596_;
                        v___y_1559_ = v___x_1609_;
                        v___y_1560_ = v___x_1603_;
                        v___y_1561_ = v___x_1611_;
                        v___y_1562_ = v___x_1606_;
                        v___y_1563_ = v___x_1610_;
                        v___y_1564_ = v___x_1614_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1619_ = leanh::lean_unsigned_to_nat(1);
                v___x_1620_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1619_);
                v___x_1621_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7;
                leanh::lean_inc(v___x_1620_);
                v___x_1622_ = l_Lean_Syntax_isOfKind(v___x_1620_, v___x_1621_);
                if v___x_1622_ == 0 {
                    leanh::lean_dec(v___x_1620_);
                    leanh::lean_dec(v_doc_x3f_1616_);
                    leanh::lean_dec(v_x_1516_);
                    v___x_1623_ = leanh::lean_box(1);
                    v___x_1624_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1624_, 0, v___x_1623_);
                    leanh::lean_ctor_set(v___x_1624_, 1, v___y_1618_);
                    return v___x_1624_;
                } else {
                    v___x_1625_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1626_ = l_Lean_Syntax_getArg(v_x_1516_, v___x_1625_);
                    v___x_1627_ = l_Lean_Syntax_isNone(v___x_1626_);
                    if v___x_1627_ == 0 {
                        leanh::lean_inc(v___x_1626_);
                        v___x_1628_ = l_Lean_Syntax_matchesNull(v___x_1626_, v___x_1619_);
                        if v___x_1628_ == 0 {
                            leanh::lean_dec(v___x_1626_);
                            leanh::lean_dec(v___x_1620_);
                            leanh::lean_dec(v_doc_x3f_1616_);
                            leanh::lean_dec(v_x_1516_);
                            v___x_1629_ = leanh::lean_box(1);
                            v___x_1630_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1630_, 0, v___x_1629_);
                            leanh::lean_ctor_set(v___x_1630_, 1, v___y_1618_);
                            return v___x_1630_;
                        } else {
                            v_phase_x3f_1631_ = l_Lean_Syntax_getArg(v___x_1626_, v___x_1551_);
                            leanh::lean_dec(v___x_1626_);
                            v___x_1632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1632_, 0, v_phase_x3f_1631_);
                            v___y_1590_ = v___x_1620_;
                            v___y_1591_ = v_doc_x3f_1616_;
                            v_phase_x3f_1592_ = v___x_1632_;
                            v___y_1593_ = v___y_1617_;
                            v___y_1594_ = v___y_1618_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1626_);
                        v___x_1633_ = leanh::lean_box(0);
                        v___y_1590_ = v___x_1620_;
                        v___y_1591_ = v_doc_x3f_1616_;
                        v_phase_x3f_1592_ = v___x_1633_;
                        v___y_1593_ = v___y_1617_;
                        v___y_1594_ = v___y_1618_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___boxed(
    mut v_x_1647_: *mut leanh::LeanObject,
    mut v_a_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1650_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1(v_x_1647_, v_a_1648_, v_a_1649_);
    leanh::lean_dec_ref(v_a_1648_);
    return v_res_1650_;
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(
    mut v_x_1652_: *mut leanh::LeanObject,
    mut v_a_1653_: *mut leanh::LeanObject,
    mut v_a_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_phase_x3f_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_phase_x3f_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: u8 = 0;
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: u8 = 0;
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1681_ = l_Lean_Parser_cbvSimprocEval___closed__1;
                v___x_1682_ = l_Lean_Parser_cbvSimprocEval___closed__2;
                v___x_1683_ = l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d___00__closed__1;
                leanh::lean_inc(v_x_1652_);
                v___x_1684_ = l_Lean_Syntax_isOfKind(v_x_1652_, v___x_1683_);
                if v___x_1684_ == 0 {
                    leanh::lean_dec(v_x_1652_);
                    v___x_1685_ = leanh::lean_box(1);
                    v___x_1686_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1686_, 0, v___x_1685_);
                    leanh::lean_ctor_set(v___x_1686_, 1, v_a_1654_);
                    return v___x_1686_;
                } else {
                    v___x_1687_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1770_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1687_);
                    v___x_1771_ = l_Lean_Syntax_isNone(v___x_1770_);
                    if v___x_1771_ == 0 {
                        v___x_1772_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1770_);
                        v___x_1773_ = l_Lean_Syntax_matchesNull(v___x_1770_, v___x_1772_);
                        if v___x_1773_ == 0 {
                            leanh::lean_dec(v___x_1770_);
                            leanh::lean_dec(v_x_1652_);
                            v___x_1774_ = leanh::lean_box(1);
                            v___x_1775_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1775_, 0, v___x_1774_);
                            leanh::lean_ctor_set(v___x_1775_, 1, v_a_1654_);
                            return v___x_1775_;
                        } else {
                            v_doc_x3f_1776_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1687_);
                            leanh::lean_dec(v___x_1770_);
                            v___x_1777_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__30;
                            leanh::lean_inc(v_doc_x3f_1776_);
                            v___x_1778_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1776_, v___x_1777_);
                            if v___x_1778_ == 0 {
                                leanh::lean_dec(v_doc_x3f_1776_);
                                leanh::lean_dec(v_x_1652_);
                                v___x_1779_ = leanh::lean_box(1);
                                v___x_1780_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1780_, 0, v___x_1779_);
                                leanh::lean_ctor_set(v___x_1780_, 1, v_a_1654_);
                                return v___x_1780_;
                            } else {
                                v___x_1781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1781_, 0, v_doc_x3f_1776_);
                                v_doc_x3f_1752_ = v___x_1781_;
                                v___y_1753_ = v_a_1653_;
                                v___y_1754_ = v_a_1654_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1770_);
                        v___x_1782_ = leanh::lean_box(0);
                        v_doc_x3f_1752_ = v___x_1782_;
                        v___y_1753_ = v_a_1653_;
                        v___y_1754_ = v_a_1654_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_1663_);
                v___x_1670_ = l_Array_append___redArg(v___y_1663_, v___y_1669_);
                leanh::lean_dec_ref(v___y_1669_);
                leanh::lean_inc_n(v___y_1664_, 4);
                leanh::lean_inc_n(v___y_1661_, 7);
                v___x_1671_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1671_, 0, v___y_1661_);
                leanh::lean_ctor_set(v___x_1671_, 1, v___y_1664_);
                leanh::lean_ctor_set(v___x_1671_, 2, v___x_1670_);
                leanh::lean_inc(v___y_1656_);
                v___x_1672_ =
                    l_Lean_Syntax_node2(v___y_1661_, v___y_1656_, v___y_1660_, v___x_1671_);
                v___x_1673_ =
                    l_Lean_Syntax_node2(v___y_1661_, v___y_1658_, v___y_1662_, v___x_1672_);
                v___x_1674_ = l_Lean_Syntax_node1(v___y_1661_, v___y_1664_, v___x_1673_);
                v___x_1675_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__0;
                v___x_1676_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1676_, 0, v___y_1661_);
                leanh::lean_ctor_set(v___x_1676_, 1, v___x_1675_);
                v___x_1677_ = l_Lean_Syntax_node1(v___y_1661_, v___y_1664_, v___y_1665_);
                leanh::lean_inc(v___y_1667_);
                v___x_1678_ = l_Lean_Syntax_node5(
                    v___y_1661_,
                    v___y_1667_,
                    v___y_1668_,
                    v___y_1659_,
                    v___x_1674_,
                    v___x_1676_,
                    v___x_1677_,
                );
                v___x_1679_ =
                    l_Lean_Syntax_node2(v___y_1661_, v___y_1664_, v___y_1666_, v___x_1678_);
                v___x_1680_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1680_, 0, v___x_1679_);
                leanh::lean_ctor_set(v___x_1680_, 1, v___y_1657_);
                return v___x_1680_;
            }
            2 => {
                leanh::lean_inc_ref(v___y_1689_);
                v___x_1701_ = l_Array_append___redArg(v___y_1689_, v___y_1700_);
                leanh::lean_dec_ref(v___y_1700_);
                leanh::lean_inc(v___y_1692_);
                leanh::lean_inc_n(v___y_1694_, 9);
                v___x_1702_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1702_, 0, v___y_1694_);
                leanh::lean_ctor_set(v___x_1702_, 1, v___y_1692_);
                leanh::lean_ctor_set(v___x_1702_, 2, v___x_1701_);
                v___x_1703_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___closed__0;
                v___x_1704_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1704_, 0, v___y_1694_);
                leanh::lean_ctor_set(v___x_1704_, 1, v___x_1703_);
                v___x_1705_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__2;
                v___x_1706_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1706_, 0, v___y_1694_);
                leanh::lean_ctor_set(v___x_1706_, 1, v___x_1705_);
                v___x_1707_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__34;
                v___x_1708_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1708_, 0, v___y_1694_);
                leanh::lean_ctor_set(v___x_1708_, 1, v___x_1707_);
                v___x_1709_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__10;
                v___x_1710_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1710_, 0, v___y_1694_);
                leanh::lean_ctor_set(v___x_1710_, 1, v___x_1709_);
                leanh::lean_inc(v___y_1695_);
                leanh::lean_inc(v___y_1693_);
                v___x_1711_ = l_Lean_Syntax_node8(
                    v___y_1694_,
                    v___y_1693_,
                    v___x_1702_,
                    v___x_1704_,
                    v___y_1695_,
                    v___x_1706_,
                    v___y_1696_,
                    v___x_1708_,
                    v___x_1710_,
                    v___y_1691_,
                );
                v___x_1712_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__3;
                v___x_1713_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__4;
                v___x_1714_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1714_, 0, v___y_1694_);
                leanh::lean_ctor_set(v___x_1714_, 1, v___x_1712_);
                v___x_1715_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__5;
                v___x_1716_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1716_, 0, v___y_1694_);
                leanh::lean_ctor_set(v___x_1716_, 1, v___x_1715_);
                v___x_1717_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__6;
                leanh::lean_inc_ref(v___y_1699_);
                v___x_1718_ =
                    l_Lean_Name_mkStr4(v___x_1681_, v___x_1682_, v___y_1699_, v___x_1717_);
                v___x_1719_ = l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__1;
                v___x_1720_ = l_Lean_Parser_Attr_cbvSimprocBuiltinAttr___closed__2;
                v___x_1721_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1721_, 0, v___y_1694_);
                leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                if leanh::lean_obj_tag(v___y_1697_) == 1 {
                    v_val_1722_ = leanh::lean_ctor_get(v___y_1697_, 0);
                    leanh::lean_inc(v_val_1722_);
                    leanh::lean_dec_ref_known(v___y_1697_, 1);
                    v___x_1723_ = l_Array_mkArray1___redArg(v_val_1722_);
                    v___y_1656_ = v___x_1719_;
                    v___y_1657_ = v___y_1690_;
                    v___y_1658_ = v___x_1718_;
                    v___y_1659_ = v___x_1716_;
                    v___y_1660_ = v___x_1721_;
                    v___y_1661_ = v___y_1694_;
                    v___y_1662_ = v___y_1698_;
                    v___y_1663_ = v___y_1689_;
                    v___y_1664_ = v___y_1692_;
                    v___y_1665_ = v___y_1695_;
                    v___y_1666_ = v___x_1711_;
                    v___y_1667_ = v___x_1713_;
                    v___y_1668_ = v___x_1714_;
                    v___y_1669_ = v___x_1723_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1697_);
                    v___x_1724_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                    v___y_1656_ = v___x_1719_;
                    v___y_1657_ = v___y_1690_;
                    v___y_1658_ = v___x_1718_;
                    v___y_1659_ = v___x_1716_;
                    v___y_1660_ = v___x_1721_;
                    v___y_1661_ = v___y_1694_;
                    v___y_1662_ = v___y_1698_;
                    v___y_1663_ = v___y_1689_;
                    v___y_1664_ = v___y_1692_;
                    v___y_1665_ = v___y_1695_;
                    v___y_1666_ = v___x_1711_;
                    v___y_1667_ = v___x_1713_;
                    v___y_1668_ = v___x_1714_;
                    v___y_1669_ = v___x_1724_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1731_ = leanh::lean_unsigned_to_nat(4);
                v___x_1732_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1731_);
                v___x_1733_ = l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d___00__closed__24;
                leanh::lean_inc(v___x_1732_);
                v___x_1734_ = l_Lean_Syntax_isOfKind(v___x_1732_, v___x_1733_);
                if v___x_1734_ == 0 {
                    leanh::lean_dec(v___x_1732_);
                    leanh::lean_dec(v_phase_x3f_1728_);
                    leanh::lean_dec(v___y_1727_);
                    leanh::lean_dec(v___y_1726_);
                    leanh::lean_dec(v_x_1652_);
                    v___x_1735_ = leanh::lean_box(1);
                    v___x_1736_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1736_, 0, v___x_1735_);
                    leanh::lean_ctor_set(v___x_1736_, 1, v___y_1730_);
                    return v___x_1736_;
                } else {
                    v_ref_1737_ = leanh::lean_ctor_get(v___y_1729_, 5);
                    v___x_1738_ = leanh::lean_unsigned_to_nat(6);
                    v___x_1739_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1738_);
                    v___x_1740_ = leanh::lean_unsigned_to_nat(9);
                    v___x_1741_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1740_);
                    leanh::lean_dec(v_x_1652_);
                    v___x_1742_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__5;
                    v___x_1743_ = 0;
                    v___x_1744_ = l_Lean_SourceInfo_fromRef(v_ref_1737_, v___x_1743_);
                    v___x_1745_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__22;
                    v___x_1746_ = l_Lean_Parser_command__Builtin__cbv__simproc__decl___x28___x29_x3a_x3d___00__closed__1;
                    v___x_1747_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28), core::ptr::addr_of_mut!(l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28_once), _init_l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__28);
                    if leanh::lean_obj_tag(v___y_1727_) == 1 {
                        v_val_1748_ = leanh::lean_ctor_get(v___y_1727_, 0);
                        leanh::lean_inc(v_val_1748_);
                        leanh::lean_dec_ref_known(v___y_1727_, 1);
                        v___x_1749_ = l_Array_mkArray1___redArg(v_val_1748_);
                        v___y_1689_ = v___x_1747_;
                        v___y_1690_ = v___y_1730_;
                        v___y_1691_ = v___x_1741_;
                        v___y_1692_ = v___x_1745_;
                        v___y_1693_ = v___x_1746_;
                        v___y_1694_ = v___x_1744_;
                        v___y_1695_ = v___x_1732_;
                        v___y_1696_ = v___x_1739_;
                        v___y_1697_ = v_phase_x3f_1728_;
                        v___y_1698_ = v___y_1726_;
                        v___y_1699_ = v___x_1742_;
                        v___y_1700_ = v___x_1749_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1727_);
                        v___x_1750_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command__Cbv__simproc__decl___x28___x29_x3a_x3d____1___closed__29;
                        v___y_1689_ = v___x_1747_;
                        v___y_1690_ = v___y_1730_;
                        v___y_1691_ = v___x_1741_;
                        v___y_1692_ = v___x_1745_;
                        v___y_1693_ = v___x_1746_;
                        v___y_1694_ = v___x_1744_;
                        v___y_1695_ = v___x_1732_;
                        v___y_1696_ = v___x_1739_;
                        v___y_1697_ = v_phase_x3f_1728_;
                        v___y_1698_ = v___y_1726_;
                        v___y_1699_ = v___x_1742_;
                        v___y_1700_ = v___x_1750_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1755_ = leanh::lean_unsigned_to_nat(1);
                v___x_1756_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1755_);
                v___x_1757_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Cbv__simproc_________x28___x29_x3a_x3d____1___closed__7;
                leanh::lean_inc(v___x_1756_);
                v___x_1758_ = l_Lean_Syntax_isOfKind(v___x_1756_, v___x_1757_);
                if v___x_1758_ == 0 {
                    leanh::lean_dec(v___x_1756_);
                    leanh::lean_dec(v_doc_x3f_1752_);
                    leanh::lean_dec(v_x_1652_);
                    v___x_1759_ = leanh::lean_box(1);
                    v___x_1760_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1760_, 0, v___x_1759_);
                    leanh::lean_ctor_set(v___x_1760_, 1, v___y_1754_);
                    return v___x_1760_;
                } else {
                    v___x_1761_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1762_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1761_);
                    v___x_1763_ = l_Lean_Syntax_isNone(v___x_1762_);
                    if v___x_1763_ == 0 {
                        leanh::lean_inc(v___x_1762_);
                        v___x_1764_ = l_Lean_Syntax_matchesNull(v___x_1762_, v___x_1755_);
                        if v___x_1764_ == 0 {
                            leanh::lean_dec(v___x_1762_);
                            leanh::lean_dec(v___x_1756_);
                            leanh::lean_dec(v_doc_x3f_1752_);
                            leanh::lean_dec(v_x_1652_);
                            v___x_1765_ = leanh::lean_box(1);
                            v___x_1766_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1766_, 0, v___x_1765_);
                            leanh::lean_ctor_set(v___x_1766_, 1, v___y_1754_);
                            return v___x_1766_;
                        } else {
                            v_phase_x3f_1767_ = l_Lean_Syntax_getArg(v___x_1762_, v___x_1687_);
                            leanh::lean_dec(v___x_1762_);
                            v___x_1768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1768_, 0, v_phase_x3f_1767_);
                            v___y_1726_ = v___x_1756_;
                            v___y_1727_ = v_doc_x3f_1752_;
                            v_phase_x3f_1728_ = v___x_1768_;
                            v___y_1729_ = v___y_1753_;
                            v___y_1730_ = v___y_1754_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1762_);
                        v___x_1769_ = leanh::lean_box(0);
                        v___y_1726_ = v___x_1756_;
                        v___y_1727_ = v_doc_x3f_1752_;
                        v_phase_x3f_1728_ = v___x_1769_;
                        v___y_1729_ = v___y_1753_;
                        v___y_1730_ = v___y_1754_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1___boxed(
    mut v_x_1783_: *mut leanh::LeanObject,
    mut v_a_1784_: *mut leanh::LeanObject,
    mut v_a_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Lean_Parser___aux__Init__CbvSimproc______macroRules__Lean__Parser__command____Builtin__cbv__simproc_________x28___x29_x3a_x3d____1(v_x_1783_, v_a_1784_, v_a_1785_);
    leanh::lean_dec_ref(v_a_1784_);
    return v_res_1786_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_CbvSimproc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_CbvSimproc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__();
    leanh::lean_mark_persistent(
        l_Lean_Parser_command____Cbv__simproc_________x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__ =
        _init_l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__();
    leanh::lean_mark_persistent(
        l_Lean_Parser_command____Builtin__cbv__simproc_________x28___x29_x3a_x3d__,
    );
    l_Lean_Parser_Attr_cbvSimprocAttr = _init_l_Lean_Parser_Attr_cbvSimprocAttr();
    leanh::lean_mark_persistent(l_Lean_Parser_Attr_cbvSimprocAttr);
    l_Lean_Parser_Attr_cbvSimprocBuiltinAttr = _init_l_Lean_Parser_Attr_cbvSimprocBuiltinAttr();
    leanh::lean_mark_persistent(l_Lean_Parser_Attr_cbvSimprocBuiltinAttr);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_CbvSimproc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_CbvSimproc(builtin);
}