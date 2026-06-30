// Lean compiler output
// Module: Init.BinderPredicates
// Imports: Init.Grind.Tactics Init.Notation Init.Meta.Defs Init.NotationExtra
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Meta::Defs::{
    initialize_Init_Meta_Defs, runtime_initialize_Init_Meta_Defs,
};
use crate::r#gen::Init::Notation::{
    initialize_Init_Notation, l_Lean_binderIdent, runtime_initialize_Init_Notation,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_Lean_binderPred_quot___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_binderPred_quot___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_binderPred_quot___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_binderPred_quot___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__3_value: leanh::LeanStringObject<5> =
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
        m_data: [113, 117, 111, 116, 0],
    };
static mut l_Lean_binderPred_quot___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__3_value) as *mut leanh::LeanObject;
static l_Lean_binderPred_quot___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_binderPred_quot___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_binderPred_quot___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_quot___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__3_value)
                as *mut leanh::LeanObject,
            5855146430765573009 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__5_value: leanh::LeanStringObject<11> =
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
        m_data: [98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 0],
    };
static mut l_Lean_binderPred_quot___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__5_value) as *mut leanh::LeanObject;
static l_Lean_binderPred_quot___closed__6_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__5_value)
                as *mut leanh::LeanObject,
            13780673489923901146 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_quot___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__3_value)
                as *mut leanh::LeanObject,
            17730888937721440716 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__7_value: leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_binderPred_quot___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__7_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__9_value: leanh::LeanStringObject<15> =
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
            96, 40, 98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 124, 32, 0,
        ],
    };
static mut l_Lean_binderPred_quot___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__10_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__5_value)
                as *mut leanh::LeanObject,
            13780673489923901146 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__11_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__13_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lean_binderPred_quot___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__14_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__6_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_quot___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__4_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_quot___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__18_value) as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_quot: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_quot___closed__18_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_Category_binderPred: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        116, 101, 114, 109, 83, 97, 116, 105, 115, 102, 105, 101, 115, 95, 98, 105, 110, 100, 101,
        114, 95, 112, 114, 101, 100, 37, 95, 95, 0,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value:
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
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__0_value)
            as *mut leanh::LeanObject,
        5900987525369307171 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__2_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        115, 97, 116, 105, 115, 102, 105, 101, 115, 95, 98, 105, 110, 100, 101, 114, 95, 112, 114,
        101, 100, 37, 32, 0,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__5_value:
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
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__4_value)
            as *mut leanh::LeanObject,
        8609355255726335675 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__5_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__7_value:
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
        core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__8_value:
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
        core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_binderPred_quot___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_termSatisfies__binder__pred_x25_____00__closed__9_value:
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
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__1_value)
            as *mut leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_termSatisfies__binder__pred_x25_____00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__9_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_termSatisfies__binder__pred_x25____: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_term_u2203_____x2c___00__closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 9,
        m_data: [116, 101, 114, 109, 226, 136, 131, 95, 95, 44, 95, 0],
    };
static mut l_Lean_term_u2203_____x2c___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_term_u2203_____x2c___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_term_u2203_____x2c___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__0_value)
                as *mut leanh::LeanObject,
            17140110321212302617 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_term_u2203_____x2c___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_term_u2203_____x2c___00__closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 2,
        m_data: [226, 136, 131, 32, 0],
    };
static mut l_Lean_term_u2203_____x2c___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_term_u2203_____x2c___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_term_u2203_____x2c___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_term_u2203_____x2c___00__closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2203_____x2c___00__closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_term_u2203_____x2c___00__closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2203_____x2c___00__closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_term_u2203_____x2c___00__closed__6_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_Lean_term_u2203_____x2c___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_term_u2203_____x2c___00__closed__7_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_term_u2203_____x2c___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_term_u2203_____x2c___00__closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2203_____x2c___00__closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_term_u2203_____x2c___00__closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_termSatisfies__binder__pred_x25_____00__closed__5_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_term_u2203_____x2c___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_term_u2203_____x2c___00__closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2203_____x2c___00__closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_term_u2203_____x2c___00__closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2203_____x2c___00__closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_term_u2203_____x2c__: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_term_u2200_____x2c___00__closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 9,
        m_data: [116, 101, 114, 109, 226, 136, 128, 95, 95, 44, 95, 0],
    };
static mut l_Lean_term_u2200_____x2c___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2200_____x2c___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_term_u2200_____x2c___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_term_u2200_____x2c___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_term_u2200_____x2c___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2200_____x2c___00__closed__0_value)
                as *mut leanh::LeanObject,
            1392184717224382588 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_term_u2200_____x2c___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2200_____x2c___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_term_u2200_____x2c___00__closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 2,
        m_data: [226, 136, 128, 32, 0],
    };
static mut l_Lean_term_u2200_____x2c___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2200_____x2c___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_term_u2200_____x2c___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_term_u2200_____x2c___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_term_u2200_____x2c___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_term_u2200_____x2c___00__closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_term_u2200_____x2c___00__closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2200_____x2c___00__closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_term_u2200_____x2c___00__closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2200_____x2c___00__closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_term_u2200_____x2c___00__closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2200_____x2c___00__closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_term_u2200_____x2c___00__closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2200_____x2c___00__closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_term_u2200_____x2c___00__closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_term_u2200_____x2c___00__closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_term_u2200_____x2c__: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__0_value) as *mut leanh::LeanObject,13771926289831477797 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__2_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__4_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__4_value) as *mut leanh::LeanObject,3984140175429830279 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__6_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 8, m_data: [116, 101, 114, 109, 226, 136, 131, 95, 44, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__6_value) as *mut leanh::LeanObject,11648432508191336928 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 136, 131, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__9_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 115, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__9_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__9_value) as *mut leanh::LeanObject,6837290835390731687 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__11_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [117, 110, 98, 114, 97, 99, 107, 101, 116, 101, 100, 69, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 115, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__11_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__11_value) as *mut leanh::LeanObject,14445138515882138811 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15_value) as *mut leanh::LeanObject,13655884332201764339 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__20_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 136, 167, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__20_value) as *mut leanh::LeanObject,16092624431164547285 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [115, 97, 116, 105, 115, 102, 105, 101, 115, 95, 98, 105, 110, 100, 101, 114, 95, 112, 114, 101, 100, 37, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 136, 167, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 111, 114, 97, 108, 108, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__0_value) as *mut leanh::LeanObject,8295462524819836611 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 136, 128, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__3_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_binderPred_quot___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__3_value) as *mut leanh::LeanObject,14917456309791986358 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 146, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3e___00__closed__0_value: leanh::LeanStringObject<13> =
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
        m_data: [98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 62, 95, 0],
    };
static mut l_Lean_binderPred_x3e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_x3e___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_x3e___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__0_value)
                as *mut leanh::LeanObject,
            3446747331573511308 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_x3e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3e___00__closed__2_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 62, 32, 0],
    };
static mut l_Lean_binderPred_x3e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3e___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_x3e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3e___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_x3e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3e___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_x3e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_x3e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 62, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__0_value) as *mut leanh::LeanObject,2001898756292774677 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [62, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2265___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 137, 165, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2265___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2265___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2265___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__0_value)
                as *mut leanh::LeanObject,
            17770506150949915604 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2265___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2265___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 137, 165, 32, 0],
    };
static mut l_Lean_binderPred_u2265___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2265___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2265___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2265___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2265___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2265___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2265___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2265__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2265___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 137, 165, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__0_value) as *mut leanh::LeanObject,15256166972235071802 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 137, 165, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3c___00__closed__0_value: leanh::LeanStringObject<13> =
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
        m_data: [98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 60, 95, 0],
    };
static mut l_Lean_binderPred_x3c___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_x3c___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_x3c___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__0_value)
                as *mut leanh::LeanObject,
            2144593201250073175 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_x3c___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3c___00__closed__2_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 60, 32, 0],
    };
static mut l_Lean_binderPred_x3c___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3c___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_x3c___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3c___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_x3c___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_x3c___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_x3c___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_x3c__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 60, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__0_value) as *mut leanh::LeanObject,6883052497475924672 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [60, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2264___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 137, 164, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2264___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2264___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2264___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__0_value)
                as *mut leanh::LeanObject,
            13608247742197726838 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2264___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2264___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 137, 164, 32, 0],
    };
static mut l_Lean_binderPred_u2264___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2264___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2264___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2264___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2264___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2264___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2264___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2264__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2264___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 137, 164, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__0_value) as *mut leanh::LeanObject,8748957123817046895 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 137, 164, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2260___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 137, 160, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2260___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2260___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2260___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__0_value)
                as *mut leanh::LeanObject,
            1408587138961057831 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2260___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2260___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 137, 160, 32, 0],
    };
static mut l_Lean_binderPred_u2260___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2260___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2260___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2260___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2260___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2260___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2260___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2260__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2260___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 137, 160, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__0_value) as *mut leanh::LeanObject,6870096354468370040 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 137, 160, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2208___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 136, 136, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2208___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2208___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2208___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__0_value)
                as *mut leanh::LeanObject,
            6664827498208863382 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2208___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2208___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 136, 136, 32, 0],
    };
static mut l_Lean_binderPred_u2208___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2208___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2208___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2208___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2208___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2208___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2208___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2208__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2208___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 136, 136, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__0_value) as *mut leanh::LeanObject,10408267619263485329 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 136, 136, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2209___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 136, 137, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2209___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2209___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2209___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__0_value)
                as *mut leanh::LeanObject,
            5078209665274543507 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2209___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2209___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 136, 137, 32, 0],
    };
static mut l_Lean_binderPred_u2209___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2209___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2209___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2209___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2209___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2209___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2209___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2209__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2209___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 136, 137, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__0_value) as *mut leanh::LeanObject,5233878110703697905 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 136, 137, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2286___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 138, 134, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2286___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2286___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2286___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__0_value)
                as *mut leanh::LeanObject,
            4537512697145268145 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2286___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2286___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 138, 134, 32, 0],
    };
static mut l_Lean_binderPred_u2286___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2286___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2286___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2286___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2286___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2286___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2286___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2286__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2286___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 138, 134, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__0_value) as *mut leanh::LeanObject,5176406056088816145 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 138, 134, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2282___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 138, 130, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2282___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2282___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2282___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__0_value)
                as *mut leanh::LeanObject,
            7753289514790772011 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2282___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2282___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 138, 130, 32, 0],
    };
static mut l_Lean_binderPred_u2282___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2282___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2282___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2282___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2282___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2282___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2282___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2282__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2282___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 138, 130, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__0_value) as *mut leanh::LeanObject,6590347383071581352 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 138, 130, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2287___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 138, 135, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2287___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2287___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2287___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__0_value)
                as *mut leanh::LeanObject,
            1519335840951422329 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2287___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2287___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 138, 135, 32, 0],
    };
static mut l_Lean_binderPred_u2287___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2287___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2287___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2287___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2287___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2287___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2287___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2287__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2287___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 138, 135, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__0_value) as *mut leanh::LeanObject,8374780288282734718 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 138, 135, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2283___00__closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 12,
        m_data: [
            98, 105, 110, 100, 101, 114, 80, 114, 101, 100, 226, 138, 131, 95, 0,
        ],
    };
static mut l_Lean_binderPred_u2283___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_binderPred_u2283___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_binderPred_u2283___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__0_value)
                as *mut leanh::LeanObject,
            13109984784226706659 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2283___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2283___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 138, 131, 32, 0],
    };
static mut l_Lean_binderPred_u2283___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2283___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2283___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2283___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_binderPred_quot___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_term_u2203_____x2c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2283___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_binderPred_u2283___00__closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_binderPred_u2283___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_binderPred_u2283__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_binderPred_u2283___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 7, m_data: [116, 101, 114, 109, 95, 226, 138, 131, 95, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__0_value) as *mut leanh::LeanObject,2941378491569920306 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 138, 131, 0]};
static mut l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Parser_Category_binderPred() -> *mut leanh::LeanObject {
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_936_ = leanh::lean_box(0);
    return v___x_936_;
}
pub unsafe fn _init_l_Lean_term_u2203_____x2c___00__closed__4() -> *mut leanh::LeanObject {
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = l_Lean_binderIdent;
    v___x_971_ = l_Lean_term_u2203_____x2c___00__closed__3;
    v___x_972_ = l_Lean_binderPred_quot___closed__8;
    v___x_973_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_973_, 0, v___x_972_);
    leanh::lean_ctor_set(v___x_973_, 1, v___x_971_);
    leanh::lean_ctor_set(v___x_973_, 2, v___x_970_);
    return v___x_973_;
}
pub unsafe fn _init_l_Lean_term_u2203_____x2c___00__closed__5() -> *mut leanh::LeanObject {
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = l_Lean_binderPred_quot___closed__12;
    v___x_975_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__4_once),
        _init_l_Lean_term_u2203_____x2c___00__closed__4,
    );
    v___x_976_ = l_Lean_binderPred_quot___closed__8;
    v___x_977_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
    leanh::lean_ctor_set(v___x_977_, 1, v___x_975_);
    leanh::lean_ctor_set(v___x_977_, 2, v___x_974_);
    return v___x_977_;
}
pub unsafe fn _init_l_Lean_term_u2203_____x2c___00__closed__8() -> *mut leanh::LeanObject {
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_981_ = l_Lean_term_u2203_____x2c___00__closed__7;
    v___x_982_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__5_once),
        _init_l_Lean_term_u2203_____x2c___00__closed__5,
    );
    v___x_983_ = l_Lean_binderPred_quot___closed__8;
    v___x_984_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_984_, 0, v___x_983_);
    leanh::lean_ctor_set(v___x_984_, 1, v___x_982_);
    leanh::lean_ctor_set(v___x_984_, 2, v___x_981_);
    return v___x_984_;
}
pub unsafe fn _init_l_Lean_term_u2203_____x2c___00__closed__10() -> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = l_Lean_term_u2203_____x2c___00__closed__9;
    v___x_989_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__8),
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__8_once),
        _init_l_Lean_term_u2203_____x2c___00__closed__8,
    );
    v___x_990_ = l_Lean_binderPred_quot___closed__8;
    v___x_991_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_991_, 0, v___x_990_);
    leanh::lean_ctor_set(v___x_991_, 1, v___x_989_);
    leanh::lean_ctor_set(v___x_991_, 2, v___x_988_);
    return v___x_991_;
}
pub unsafe fn _init_l_Lean_term_u2203_____x2c___00__closed__11() -> *mut leanh::LeanObject {
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__10),
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__10_once),
        _init_l_Lean_term_u2203_____x2c___00__closed__10,
    );
    v___x_993_ = leanh::lean_unsigned_to_nat(1022);
    v___x_994_ = l_Lean_term_u2203_____x2c___00__closed__1;
    v___x_995_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_995_, 0, v___x_994_);
    leanh::lean_ctor_set(v___x_995_, 1, v___x_993_);
    leanh::lean_ctor_set(v___x_995_, 2, v___x_992_);
    return v___x_995_;
}
pub unsafe fn _init_l_Lean_term_u2203_____x2c__() -> *mut leanh::LeanObject {
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_996_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__11),
        core::ptr::addr_of_mut!(l_Lean_term_u2203_____x2c___00__closed__11_once),
        _init_l_Lean_term_u2203_____x2c___00__closed__11,
    );
    return v___x_996_;
}
pub unsafe fn _init_l_Lean_term_u2200_____x2c___00__closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = l_Lean_binderIdent;
    v___x_1005_ = l_Lean_term_u2200_____x2c___00__closed__3;
    v___x_1006_ = l_Lean_binderPred_quot___closed__8;
    v___x_1007_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1007_, 0, v___x_1006_);
    leanh::lean_ctor_set(v___x_1007_, 1, v___x_1005_);
    leanh::lean_ctor_set(v___x_1007_, 2, v___x_1004_);
    return v___x_1007_;
}
pub unsafe fn _init_l_Lean_term_u2200_____x2c___00__closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1008_ = l_Lean_binderPred_quot___closed__12;
    v___x_1009_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__4_once),
        _init_l_Lean_term_u2200_____x2c___00__closed__4,
    );
    v___x_1010_ = l_Lean_binderPred_quot___closed__8;
    v___x_1011_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1011_, 0, v___x_1010_);
    leanh::lean_ctor_set(v___x_1011_, 1, v___x_1009_);
    leanh::lean_ctor_set(v___x_1011_, 2, v___x_1008_);
    return v___x_1011_;
}
pub unsafe fn _init_l_Lean_term_u2200_____x2c___00__closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = l_Lean_term_u2203_____x2c___00__closed__7;
    v___x_1013_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__5_once),
        _init_l_Lean_term_u2200_____x2c___00__closed__5,
    );
    v___x_1014_ = l_Lean_binderPred_quot___closed__8;
    v___x_1015_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1015_, 0, v___x_1014_);
    leanh::lean_ctor_set(v___x_1015_, 1, v___x_1013_);
    leanh::lean_ctor_set(v___x_1015_, 2, v___x_1012_);
    return v___x_1015_;
}
pub unsafe fn _init_l_Lean_term_u2200_____x2c___00__closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = l_Lean_term_u2203_____x2c___00__closed__9;
    v___x_1017_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__6),
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__6_once),
        _init_l_Lean_term_u2200_____x2c___00__closed__6,
    );
    v___x_1018_ = l_Lean_binderPred_quot___closed__8;
    v___x_1019_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    leanh::lean_ctor_set(v___x_1019_, 1, v___x_1017_);
    leanh::lean_ctor_set(v___x_1019_, 2, v___x_1016_);
    return v___x_1019_;
}
pub unsafe fn _init_l_Lean_term_u2200_____x2c___00__closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__7),
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__7_once),
        _init_l_Lean_term_u2200_____x2c___00__closed__7,
    );
    v___x_1021_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1022_ = l_Lean_term_u2200_____x2c___00__closed__1;
    v___x_1023_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1023_, 0, v___x_1022_);
    leanh::lean_ctor_set(v___x_1023_, 1, v___x_1021_);
    leanh::lean_ctor_set(v___x_1023_, 2, v___x_1020_);
    return v___x_1023_;
}
pub unsafe fn _init_l_Lean_term_u2200_____x2c__() -> *mut leanh::LeanObject {
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1024_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__8),
        core::ptr::addr_of_mut!(l_Lean_term_u2200_____x2c___00__closed__8_once),
        _init_l_Lean_term_u2200_____x2c___00__closed__8,
    );
    return v___x_1024_;
}
pub unsafe fn _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__15;
    v___x_1055_ = l_String_toRawSubstring_x27(v___x_1054_);
    return v___x_1055_;
}
pub unsafe fn _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1058_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1(
    mut v_x_1065_: *mut leanh::LeanObject,
    mut v_a_1066_: *mut leanh::LeanObject,
    mut v_a_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: u8 = 0;
    v___x_1068_ = l_Lean_term_u2203_____x2c___00__closed__1;
    leanh::lean_inc(v_x_1065_);
    v___x_1069_ = l_Lean_Syntax_isOfKind(v_x_1065_, v___x_1068_);
    if v___x_1069_ == 0 {
        let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1065_);
        v___x_1070_ = leanh::lean_box(1);
        v___x_1071_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1071_, 0, v___x_1070_);
        leanh::lean_ctor_set(v___x_1071_, 1, v_a_1067_);
        return v___x_1071_;
    } else {
        let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1075_: u8 = 0;
        v___x_1072_ = leanh::lean_unsigned_to_nat(1);
        v___x_1073_ = l_Lean_Syntax_getArg(v_x_1065_, v___x_1072_);
        v___x_1074_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1;
        leanh::lean_inc(v___x_1073_);
        v___x_1075_ = l_Lean_Syntax_isOfKind(v___x_1073_, v___x_1074_);
        if v___x_1075_ == 0 {
            let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1073_);
            leanh::lean_dec(v_x_1065_);
            v___x_1076_ = leanh::lean_box(1);
            v___x_1077_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1077_, 0, v___x_1076_);
            leanh::lean_ctor_set(v___x_1077_, 1, v_a_1067_);
            return v___x_1077_;
        } else {
            let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1081_: u8 = 0;
            v___x_1078_ = leanh::lean_unsigned_to_nat(0);
            v___x_1079_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_1078_);
            leanh::lean_dec(v___x_1073_);
            v___x_1080_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3;
            leanh::lean_inc(v___x_1079_);
            v___x_1081_ = l_Lean_Syntax_isOfKind(v___x_1079_, v___x_1080_);
            if v___x_1081_ == 0 {
                let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1083_: u8 = 0;
                v___x_1082_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5;
                v___x_1083_ = l_Lean_Syntax_isOfKind(v___x_1079_, v___x_1082_);
                if v___x_1083_ == 0 {
                    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_x_1065_);
                    v___x_1084_ = leanh::lean_box(1);
                    v___x_1085_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1085_, 0, v___x_1084_);
                    leanh::lean_ctor_set(v___x_1085_, 1, v_a_1067_);
                    return v___x_1085_;
                } else {
                    let mut v_quotContext_1086_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_currMacroScope_1087_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_ref_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_quotContext_1086_ = leanh::lean_ctor_get(v_a_1066_, 1);
                    v_currMacroScope_1087_ = leanh::lean_ctor_get(v_a_1066_, 2);
                    v_ref_1088_ = leanh::lean_ctor_get(v_a_1066_, 5);
                    v___x_1089_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1090_ = l_Lean_Syntax_getArg(v_x_1065_, v___x_1089_);
                    v___x_1091_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1092_ = l_Lean_Syntax_getArg(v_x_1065_, v___x_1091_);
                    leanh::lean_dec(v_x_1065_);
                    v___x_1093_ = l_Lean_SourceInfo_fromRef(v_ref_1088_, v___x_1081_);
                    v___x_1094_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7;
                    v___x_1095_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8;
                    leanh::lean_inc_n(v___x_1093_, 12);
                    v___x_1096_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1096_, 0, v___x_1093_);
                    leanh::lean_ctor_set(v___x_1096_, 1, v___x_1095_);
                    v___x_1097_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10;
                    v___x_1098_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12;
                    v___x_1099_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14;
                    v___x_1100_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16), core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16_once), _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16);
                    v___x_1101_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17;
                    leanh::lean_inc(v_currMacroScope_1087_);
                    leanh::lean_inc(v_quotContext_1086_);
                    v___x_1102_ = l_Lean_addMacroScope(
                        v_quotContext_1086_,
                        v___x_1101_,
                        v_currMacroScope_1087_,
                    );
                    v___x_1103_ = leanh::lean_box(0);
                    v___x_1104_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_1104_, 0, v___x_1093_);
                    leanh::lean_ctor_set(v___x_1104_, 1, v___x_1100_);
                    leanh::lean_ctor_set(v___x_1104_, 2, v___x_1102_);
                    leanh::lean_ctor_set(v___x_1104_, 3, v___x_1103_);
                    leanh::lean_inc_ref(v___x_1104_);
                    v___x_1105_ = l_Lean_Syntax_node1(v___x_1093_, v___x_1074_, v___x_1104_);
                    v___x_1106_ = l_Lean_Syntax_node1(v___x_1093_, v___x_1099_, v___x_1105_);
                    v___x_1107_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18), core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once), _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
                    v___x_1108_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1108_, 0, v___x_1093_);
                    leanh::lean_ctor_set(v___x_1108_, 1, v___x_1099_);
                    leanh::lean_ctor_set(v___x_1108_, 2, v___x_1107_);
                    v___x_1109_ =
                        l_Lean_Syntax_node2(v___x_1093_, v___x_1098_, v___x_1106_, v___x_1108_);
                    v___x_1110_ = l_Lean_Syntax_node1(v___x_1093_, v___x_1097_, v___x_1109_);
                    v___x_1111_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19;
                    v___x_1112_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1112_, 0, v___x_1093_);
                    leanh::lean_ctor_set(v___x_1112_, 1, v___x_1111_);
                    v___x_1113_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21;
                    v___x_1114_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
                    v___x_1115_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22;
                    v___x_1116_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1116_, 0, v___x_1093_);
                    leanh::lean_ctor_set(v___x_1116_, 1, v___x_1115_);
                    v___x_1117_ = l_Lean_Syntax_node3(
                        v___x_1093_,
                        v___x_1114_,
                        v___x_1116_,
                        v___x_1104_,
                        v___x_1090_,
                    );
                    v___x_1118_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23;
                    v___x_1119_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1119_, 0, v___x_1093_);
                    leanh::lean_ctor_set(v___x_1119_, 1, v___x_1118_);
                    v___x_1120_ = l_Lean_Syntax_node3(
                        v___x_1093_,
                        v___x_1113_,
                        v___x_1117_,
                        v___x_1119_,
                        v___x_1092_,
                    );
                    v___x_1121_ = l_Lean_Syntax_node4(
                        v___x_1093_,
                        v___x_1094_,
                        v___x_1096_,
                        v___x_1110_,
                        v___x_1112_,
                        v___x_1120_,
                    );
                    v___x_1122_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1122_, 0, v___x_1121_);
                    leanh::lean_ctor_set(v___x_1122_, 1, v_a_1067_);
                    return v___x_1122_;
                }
            } else {
                let mut v_ref_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1128_: u8 = 0;
                let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_ref_1123_ = leanh::lean_ctor_get(v_a_1066_, 5);
                v___x_1124_ = leanh::lean_unsigned_to_nat(2);
                v___x_1125_ = l_Lean_Syntax_getArg(v_x_1065_, v___x_1124_);
                v___x_1126_ = leanh::lean_unsigned_to_nat(4);
                v___x_1127_ = l_Lean_Syntax_getArg(v_x_1065_, v___x_1126_);
                leanh::lean_dec(v_x_1065_);
                v___x_1128_ = 0;
                v___x_1129_ = l_Lean_SourceInfo_fromRef(v_ref_1123_, v___x_1128_);
                v___x_1130_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__7;
                v___x_1131_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__8;
                leanh::lean_inc_n(v___x_1129_, 11);
                v___x_1132_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1132_, 0, v___x_1129_);
                leanh::lean_ctor_set(v___x_1132_, 1, v___x_1131_);
                v___x_1133_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__10;
                v___x_1134_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__12;
                v___x_1135_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14;
                leanh::lean_inc(v___x_1079_);
                v___x_1136_ = l_Lean_Syntax_node1(v___x_1129_, v___x_1074_, v___x_1079_);
                v___x_1137_ = l_Lean_Syntax_node1(v___x_1129_, v___x_1135_, v___x_1136_);
                v___x_1138_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18), core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once), _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
                v___x_1139_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1139_, 0, v___x_1129_);
                leanh::lean_ctor_set(v___x_1139_, 1, v___x_1135_);
                leanh::lean_ctor_set(v___x_1139_, 2, v___x_1138_);
                v___x_1140_ =
                    l_Lean_Syntax_node2(v___x_1129_, v___x_1134_, v___x_1137_, v___x_1139_);
                v___x_1141_ = l_Lean_Syntax_node1(v___x_1129_, v___x_1133_, v___x_1140_);
                v___x_1142_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19;
                v___x_1143_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1143_, 0, v___x_1129_);
                leanh::lean_ctor_set(v___x_1143_, 1, v___x_1142_);
                v___x_1144_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__21;
                v___x_1145_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
                v___x_1146_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22;
                v___x_1147_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1147_, 0, v___x_1129_);
                leanh::lean_ctor_set(v___x_1147_, 1, v___x_1146_);
                v___x_1148_ = l_Lean_Syntax_node3(
                    v___x_1129_,
                    v___x_1145_,
                    v___x_1147_,
                    v___x_1079_,
                    v___x_1125_,
                );
                v___x_1149_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__23;
                v___x_1150_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1150_, 0, v___x_1129_);
                leanh::lean_ctor_set(v___x_1150_, 1, v___x_1149_);
                v___x_1151_ = l_Lean_Syntax_node3(
                    v___x_1129_,
                    v___x_1144_,
                    v___x_1148_,
                    v___x_1150_,
                    v___x_1127_,
                );
                v___x_1152_ = l_Lean_Syntax_node4(
                    v___x_1129_,
                    v___x_1130_,
                    v___x_1132_,
                    v___x_1141_,
                    v___x_1143_,
                    v___x_1151_,
                );
                v___x_1153_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1153_, 0, v___x_1152_);
                leanh::lean_ctor_set(v___x_1153_, 1, v_a_1067_);
                return v___x_1153_;
            }
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___boxed(
    mut v_x_1154_: *mut leanh::LeanObject,
    mut v_a_1155_: *mut leanh::LeanObject,
    mut v_a_1156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1157_ =
        l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1(
            v_x_1154_, v_a_1155_, v_a_1156_,
        );
    leanh::lean_dec_ref(v_a_1155_);
    return v_res_1157_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1(
    mut v_x_1172_: *mut leanh::LeanObject,
    mut v_a_1173_: *mut leanh::LeanObject,
    mut v_a_1174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    v___x_1175_ = l_Lean_term_u2200_____x2c___00__closed__1;
    leanh::lean_inc(v_x_1172_);
    v___x_1176_ = l_Lean_Syntax_isOfKind(v_x_1172_, v___x_1175_);
    if v___x_1176_ == 0 {
        let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1172_);
        v___x_1177_ = leanh::lean_box(1);
        v___x_1178_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1178_, 0, v___x_1177_);
        leanh::lean_ctor_set(v___x_1178_, 1, v_a_1174_);
        return v___x_1178_;
    } else {
        let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: u8 = 0;
        v___x_1179_ = leanh::lean_unsigned_to_nat(1);
        v___x_1180_ = l_Lean_Syntax_getArg(v_x_1172_, v___x_1179_);
        v___x_1181_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__1;
        leanh::lean_inc(v___x_1180_);
        v___x_1182_ = l_Lean_Syntax_isOfKind(v___x_1180_, v___x_1181_);
        if v___x_1182_ == 0 {
            let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1180_);
            leanh::lean_dec(v_x_1172_);
            v___x_1183_ = leanh::lean_box(1);
            v___x_1184_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1184_, 0, v___x_1183_);
            leanh::lean_ctor_set(v___x_1184_, 1, v_a_1174_);
            return v___x_1184_;
        } else {
            let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1188_: u8 = 0;
            v___x_1185_ = leanh::lean_unsigned_to_nat(0);
            v___x_1186_ = l_Lean_Syntax_getArg(v___x_1180_, v___x_1185_);
            leanh::lean_dec(v___x_1180_);
            v___x_1187_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__3;
            leanh::lean_inc(v___x_1186_);
            v___x_1188_ = l_Lean_Syntax_isOfKind(v___x_1186_, v___x_1187_);
            if v___x_1188_ == 0 {
                let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1190_: u8 = 0;
                v___x_1189_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__5;
                v___x_1190_ = l_Lean_Syntax_isOfKind(v___x_1186_, v___x_1189_);
                if v___x_1190_ == 0 {
                    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_x_1172_);
                    v___x_1191_ = leanh::lean_box(1);
                    v___x_1192_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1192_, 0, v___x_1191_);
                    leanh::lean_ctor_set(v___x_1192_, 1, v_a_1174_);
                    return v___x_1192_;
                } else {
                    let mut v_quotContext_1193_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_currMacroScope_1194_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_ref_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_quotContext_1193_ = leanh::lean_ctor_get(v_a_1173_, 1);
                    v_currMacroScope_1194_ = leanh::lean_ctor_get(v_a_1173_, 2);
                    v_ref_1195_ = leanh::lean_ctor_get(v_a_1173_, 5);
                    v___x_1196_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1197_ = l_Lean_Syntax_getArg(v_x_1172_, v___x_1196_);
                    v___x_1198_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1199_ = l_Lean_Syntax_getArg(v_x_1172_, v___x_1198_);
                    leanh::lean_dec(v_x_1172_);
                    v___x_1200_ = l_Lean_SourceInfo_fromRef(v_ref_1195_, v___x_1188_);
                    v___x_1201_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1;
                    v___x_1202_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2;
                    leanh::lean_inc_n(v___x_1200_, 9);
                    v___x_1203_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1203_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v___x_1203_, 1, v___x_1202_);
                    v___x_1204_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14;
                    v___x_1205_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16), core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16_once), _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__16);
                    v___x_1206_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__17;
                    leanh::lean_inc(v_currMacroScope_1194_);
                    leanh::lean_inc(v_quotContext_1193_);
                    v___x_1207_ = l_Lean_addMacroScope(
                        v_quotContext_1193_,
                        v___x_1206_,
                        v_currMacroScope_1194_,
                    );
                    v___x_1208_ = leanh::lean_box(0);
                    v___x_1209_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_1209_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v___x_1209_, 1, v___x_1205_);
                    leanh::lean_ctor_set(v___x_1209_, 2, v___x_1207_);
                    leanh::lean_ctor_set(v___x_1209_, 3, v___x_1208_);
                    leanh::lean_inc_ref(v___x_1209_);
                    v___x_1210_ = l_Lean_Syntax_node1(v___x_1200_, v___x_1204_, v___x_1209_);
                    v___x_1211_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18), core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once), _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
                    v___x_1212_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1212_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v___x_1212_, 1, v___x_1204_);
                    leanh::lean_ctor_set(v___x_1212_, 2, v___x_1211_);
                    v___x_1213_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19;
                    v___x_1214_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v___x_1214_, 1, v___x_1213_);
                    v___x_1215_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4;
                    v___x_1216_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
                    v___x_1217_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22;
                    v___x_1218_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1218_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v___x_1218_, 1, v___x_1217_);
                    v___x_1219_ = l_Lean_Syntax_node3(
                        v___x_1200_,
                        v___x_1216_,
                        v___x_1218_,
                        v___x_1209_,
                        v___x_1197_,
                    );
                    v___x_1220_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5;
                    v___x_1221_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1221_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v___x_1221_, 1, v___x_1220_);
                    v___x_1222_ = l_Lean_Syntax_node3(
                        v___x_1200_,
                        v___x_1215_,
                        v___x_1219_,
                        v___x_1221_,
                        v___x_1199_,
                    );
                    v___x_1223_ = l_Lean_Syntax_node5(
                        v___x_1200_,
                        v___x_1201_,
                        v___x_1203_,
                        v___x_1210_,
                        v___x_1212_,
                        v___x_1214_,
                        v___x_1222_,
                    );
                    v___x_1224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1224_, 0, v___x_1223_);
                    leanh::lean_ctor_set(v___x_1224_, 1, v_a_1174_);
                    return v___x_1224_;
                }
            } else {
                let mut v_ref_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1230_: u8 = 0;
                let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_ref_1225_ = leanh::lean_ctor_get(v_a_1173_, 5);
                v___x_1226_ = leanh::lean_unsigned_to_nat(2);
                v___x_1227_ = l_Lean_Syntax_getArg(v_x_1172_, v___x_1226_);
                v___x_1228_ = leanh::lean_unsigned_to_nat(4);
                v___x_1229_ = l_Lean_Syntax_getArg(v_x_1172_, v___x_1228_);
                leanh::lean_dec(v_x_1172_);
                v___x_1230_ = 0;
                v___x_1231_ = l_Lean_SourceInfo_fromRef(v_ref_1225_, v___x_1230_);
                v___x_1232_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__1;
                v___x_1233_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__2;
                leanh::lean_inc_n(v___x_1231_, 8);
                v___x_1234_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1234_, 0, v___x_1231_);
                leanh::lean_ctor_set(v___x_1234_, 1, v___x_1233_);
                v___x_1235_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__14;
                leanh::lean_inc(v___x_1186_);
                v___x_1236_ = l_Lean_Syntax_node1(v___x_1231_, v___x_1235_, v___x_1186_);
                v___x_1237_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18), core::ptr::addr_of_mut!(l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18_once), _init_l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__18);
                v___x_1238_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1238_, 0, v___x_1231_);
                leanh::lean_ctor_set(v___x_1238_, 1, v___x_1235_);
                leanh::lean_ctor_set(v___x_1238_, 2, v___x_1237_);
                v___x_1239_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__19;
                v___x_1240_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1240_, 0, v___x_1231_);
                leanh::lean_ctor_set(v___x_1240_, 1, v___x_1239_);
                v___x_1241_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__4;
                v___x_1242_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
                v___x_1243_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2203_____x2c____1___closed__22;
                v___x_1244_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1244_, 0, v___x_1231_);
                leanh::lean_ctor_set(v___x_1244_, 1, v___x_1243_);
                v___x_1245_ = l_Lean_Syntax_node3(
                    v___x_1231_,
                    v___x_1242_,
                    v___x_1244_,
                    v___x_1186_,
                    v___x_1227_,
                );
                v___x_1246_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___closed__5;
                v___x_1247_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1247_, 0, v___x_1231_);
                leanh::lean_ctor_set(v___x_1247_, 1, v___x_1246_);
                v___x_1248_ = l_Lean_Syntax_node3(
                    v___x_1231_,
                    v___x_1241_,
                    v___x_1245_,
                    v___x_1247_,
                    v___x_1229_,
                );
                v___x_1249_ = l_Lean_Syntax_node5(
                    v___x_1231_,
                    v___x_1232_,
                    v___x_1234_,
                    v___x_1236_,
                    v___x_1238_,
                    v___x_1240_,
                    v___x_1248_,
                );
                v___x_1250_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
                leanh::lean_ctor_set(v___x_1250_, 1, v_a_1174_);
                return v___x_1250_;
            }
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1___boxed(
    mut v_x_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
    mut v_a_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ =
        l_Lean___aux__Init__BinderPredicates______macroRules__Lean__term_u2200_____x2c____1(
            v_x_1251_, v_a_1252_, v_a_1253_,
        );
    leanh::lean_dec_ref(v_a_1252_);
    return v_res_1254_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1(
    mut v_x_1275_: *mut leanh::LeanObject,
    mut v_a_1276_: *mut leanh::LeanObject,
    mut v_a_1277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u8 = 0;
    v___x_1278_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1275_);
    v___x_1279_ = l_Lean_Syntax_isOfKind(v_x_1275_, v___x_1278_);
    if v___x_1279_ == 0 {
        let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1275_);
        v___x_1280_ = leanh::lean_box(1);
        v___x_1281_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1281_, 0, v___x_1280_);
        leanh::lean_ctor_set(v___x_1281_, 1, v_a_1277_);
        return v___x_1281_;
    } else {
        let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1285_: u8 = 0;
        v___x_1282_ = leanh::lean_unsigned_to_nat(2);
        v___x_1283_ = l_Lean_Syntax_getArg(v_x_1275_, v___x_1282_);
        v___x_1284_ = l_Lean_binderPred_x3e___00__closed__1;
        leanh::lean_inc(v___x_1283_);
        v___x_1285_ = l_Lean_Syntax_isOfKind(v___x_1283_, v___x_1284_);
        if v___x_1285_ == 0 {
            let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1283_);
            leanh::lean_dec(v_x_1275_);
            v___x_1286_ = leanh::lean_box(1);
            v___x_1287_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1287_, 0, v___x_1286_);
            leanh::lean_ctor_set(v___x_1287_, 1, v_a_1277_);
            return v___x_1287_;
        } else {
            let mut v_ref_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1292_: u8 = 0;
            let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1288_ = leanh::lean_ctor_get(v_a_1276_, 5);
            v___x_1289_ = leanh::lean_unsigned_to_nat(1);
            v___x_1290_ = l_Lean_Syntax_getArg(v_x_1275_, v___x_1289_);
            leanh::lean_dec(v_x_1275_);
            v___x_1291_ = l_Lean_Syntax_getArg(v___x_1283_, v___x_1289_);
            leanh::lean_dec(v___x_1283_);
            v___x_1292_ = 0;
            v___x_1293_ = l_Lean_SourceInfo_fromRef(v_ref_1288_, v___x_1292_);
            v___x_1294_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__1;
            v___x_1295_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___closed__2;
            leanh::lean_inc(v___x_1293_);
            v___x_1296_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1296_, 0, v___x_1293_);
            leanh::lean_ctor_set(v___x_1296_, 1, v___x_1295_);
            v___x_1297_ = l_Lean_Syntax_node3(
                v___x_1293_,
                v___x_1294_,
                v___x_1290_,
                v___x_1296_,
                v___x_1291_,
            );
            v___x_1298_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1298_, 0, v___x_1297_);
            leanh::lean_ctor_set(v___x_1298_, 1, v_a_1277_);
            return v___x_1298_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1___boxed(
    mut v_x_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
    mut v_a_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______1(v_x_1299_, v_a_1300_, v_a_1301_);
    leanh::lean_dec_ref(v_a_1300_);
    return v_res_1302_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2(
    mut v_x_1323_: *mut leanh::LeanObject,
    mut v_a_1324_: *mut leanh::LeanObject,
    mut v_a_1325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    v___x_1326_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1323_);
    v___x_1327_ = l_Lean_Syntax_isOfKind(v_x_1323_, v___x_1326_);
    if v___x_1327_ == 0 {
        let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1323_);
        v___x_1328_ = leanh::lean_box(1);
        v___x_1329_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1329_, 0, v___x_1328_);
        leanh::lean_ctor_set(v___x_1329_, 1, v_a_1325_);
        return v___x_1329_;
    } else {
        let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: u8 = 0;
        v___x_1330_ = leanh::lean_unsigned_to_nat(2);
        v___x_1331_ = l_Lean_Syntax_getArg(v_x_1323_, v___x_1330_);
        v___x_1332_ = l_Lean_binderPred_u2265___00__closed__1;
        leanh::lean_inc(v___x_1331_);
        v___x_1333_ = l_Lean_Syntax_isOfKind(v___x_1331_, v___x_1332_);
        if v___x_1333_ == 0 {
            let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1331_);
            leanh::lean_dec(v_x_1323_);
            v___x_1334_ = leanh::lean_box(1);
            v___x_1335_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1335_, 0, v___x_1334_);
            leanh::lean_ctor_set(v___x_1335_, 1, v_a_1325_);
            return v___x_1335_;
        } else {
            let mut v_ref_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1340_: u8 = 0;
            let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1336_ = leanh::lean_ctor_get(v_a_1324_, 5);
            v___x_1337_ = leanh::lean_unsigned_to_nat(1);
            v___x_1338_ = l_Lean_Syntax_getArg(v_x_1323_, v___x_1337_);
            leanh::lean_dec(v_x_1323_);
            v___x_1339_ = l_Lean_Syntax_getArg(v___x_1331_, v___x_1337_);
            leanh::lean_dec(v___x_1331_);
            v___x_1340_ = 0;
            v___x_1341_ = l_Lean_SourceInfo_fromRef(v_ref_1336_, v___x_1340_);
            v___x_1342_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__1;
            v___x_1343_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___closed__2;
            leanh::lean_inc(v___x_1341_);
            v___x_1344_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1344_, 0, v___x_1341_);
            leanh::lean_ctor_set(v___x_1344_, 1, v___x_1343_);
            v___x_1345_ = l_Lean_Syntax_node3(
                v___x_1341_,
                v___x_1342_,
                v___x_1338_,
                v___x_1344_,
                v___x_1339_,
            );
            v___x_1346_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1346_, 0, v___x_1345_);
            leanh::lean_ctor_set(v___x_1346_, 1, v_a_1325_);
            return v___x_1346_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2___boxed(
    mut v_x_1347_: *mut leanh::LeanObject,
    mut v_a_1348_: *mut leanh::LeanObject,
    mut v_a_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1350_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______2(v_x_1347_, v_a_1348_, v_a_1349_);
    leanh::lean_dec_ref(v_a_1348_);
    return v_res_1350_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3(
    mut v_x_1371_: *mut leanh::LeanObject,
    mut v_a_1372_: *mut leanh::LeanObject,
    mut v_a_1373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    v___x_1374_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1371_);
    v___x_1375_ = l_Lean_Syntax_isOfKind(v_x_1371_, v___x_1374_);
    if v___x_1375_ == 0 {
        let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1371_);
        v___x_1376_ = leanh::lean_box(1);
        v___x_1377_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1377_, 0, v___x_1376_);
        leanh::lean_ctor_set(v___x_1377_, 1, v_a_1373_);
        return v___x_1377_;
    } else {
        let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1381_: u8 = 0;
        v___x_1378_ = leanh::lean_unsigned_to_nat(2);
        v___x_1379_ = l_Lean_Syntax_getArg(v_x_1371_, v___x_1378_);
        v___x_1380_ = l_Lean_binderPred_x3c___00__closed__1;
        leanh::lean_inc(v___x_1379_);
        v___x_1381_ = l_Lean_Syntax_isOfKind(v___x_1379_, v___x_1380_);
        if v___x_1381_ == 0 {
            let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1379_);
            leanh::lean_dec(v_x_1371_);
            v___x_1382_ = leanh::lean_box(1);
            v___x_1383_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1383_, 0, v___x_1382_);
            leanh::lean_ctor_set(v___x_1383_, 1, v_a_1373_);
            return v___x_1383_;
        } else {
            let mut v_ref_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1388_: u8 = 0;
            let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1384_ = leanh::lean_ctor_get(v_a_1372_, 5);
            v___x_1385_ = leanh::lean_unsigned_to_nat(1);
            v___x_1386_ = l_Lean_Syntax_getArg(v_x_1371_, v___x_1385_);
            leanh::lean_dec(v_x_1371_);
            v___x_1387_ = l_Lean_Syntax_getArg(v___x_1379_, v___x_1385_);
            leanh::lean_dec(v___x_1379_);
            v___x_1388_ = 0;
            v___x_1389_ = l_Lean_SourceInfo_fromRef(v_ref_1384_, v___x_1388_);
            v___x_1390_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__1;
            v___x_1391_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___closed__2;
            leanh::lean_inc(v___x_1389_);
            v___x_1392_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1392_, 0, v___x_1389_);
            leanh::lean_ctor_set(v___x_1392_, 1, v___x_1391_);
            v___x_1393_ = l_Lean_Syntax_node3(
                v___x_1389_,
                v___x_1390_,
                v___x_1386_,
                v___x_1392_,
                v___x_1387_,
            );
            v___x_1394_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1394_, 0, v___x_1393_);
            leanh::lean_ctor_set(v___x_1394_, 1, v_a_1373_);
            return v___x_1394_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3___boxed(
    mut v_x_1395_: *mut leanh::LeanObject,
    mut v_a_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______3(v_x_1395_, v_a_1396_, v_a_1397_);
    leanh::lean_dec_ref(v_a_1396_);
    return v_res_1398_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4(
    mut v_x_1419_: *mut leanh::LeanObject,
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: u8 = 0;
    v___x_1422_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1419_);
    v___x_1423_ = l_Lean_Syntax_isOfKind(v_x_1419_, v___x_1422_);
    if v___x_1423_ == 0 {
        let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1419_);
        v___x_1424_ = leanh::lean_box(1);
        v___x_1425_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1425_, 0, v___x_1424_);
        leanh::lean_ctor_set(v___x_1425_, 1, v_a_1421_);
        return v___x_1425_;
    } else {
        let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1429_: u8 = 0;
        v___x_1426_ = leanh::lean_unsigned_to_nat(2);
        v___x_1427_ = l_Lean_Syntax_getArg(v_x_1419_, v___x_1426_);
        v___x_1428_ = l_Lean_binderPred_u2264___00__closed__1;
        leanh::lean_inc(v___x_1427_);
        v___x_1429_ = l_Lean_Syntax_isOfKind(v___x_1427_, v___x_1428_);
        if v___x_1429_ == 0 {
            let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1427_);
            leanh::lean_dec(v_x_1419_);
            v___x_1430_ = leanh::lean_box(1);
            v___x_1431_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1431_, 0, v___x_1430_);
            leanh::lean_ctor_set(v___x_1431_, 1, v_a_1421_);
            return v___x_1431_;
        } else {
            let mut v_ref_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1436_: u8 = 0;
            let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1432_ = leanh::lean_ctor_get(v_a_1420_, 5);
            v___x_1433_ = leanh::lean_unsigned_to_nat(1);
            v___x_1434_ = l_Lean_Syntax_getArg(v_x_1419_, v___x_1433_);
            leanh::lean_dec(v_x_1419_);
            v___x_1435_ = l_Lean_Syntax_getArg(v___x_1427_, v___x_1433_);
            leanh::lean_dec(v___x_1427_);
            v___x_1436_ = 0;
            v___x_1437_ = l_Lean_SourceInfo_fromRef(v_ref_1432_, v___x_1436_);
            v___x_1438_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__1;
            v___x_1439_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___closed__2;
            leanh::lean_inc(v___x_1437_);
            v___x_1440_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1440_, 0, v___x_1437_);
            leanh::lean_ctor_set(v___x_1440_, 1, v___x_1439_);
            v___x_1441_ = l_Lean_Syntax_node3(
                v___x_1437_,
                v___x_1438_,
                v___x_1434_,
                v___x_1440_,
                v___x_1435_,
            );
            v___x_1442_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1442_, 0, v___x_1441_);
            leanh::lean_ctor_set(v___x_1442_, 1, v_a_1421_);
            return v___x_1442_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4___boxed(
    mut v_x_1443_: *mut leanh::LeanObject,
    mut v_a_1444_: *mut leanh::LeanObject,
    mut v_a_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______4(v_x_1443_, v_a_1444_, v_a_1445_);
    leanh::lean_dec_ref(v_a_1444_);
    return v_res_1446_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5(
    mut v_x_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    v___x_1470_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1467_);
    v___x_1471_ = l_Lean_Syntax_isOfKind(v_x_1467_, v___x_1470_);
    if v___x_1471_ == 0 {
        let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1467_);
        v___x_1472_ = leanh::lean_box(1);
        v___x_1473_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1473_, 0, v___x_1472_);
        leanh::lean_ctor_set(v___x_1473_, 1, v_a_1469_);
        return v___x_1473_;
    } else {
        let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: u8 = 0;
        v___x_1474_ = leanh::lean_unsigned_to_nat(2);
        v___x_1475_ = l_Lean_Syntax_getArg(v_x_1467_, v___x_1474_);
        v___x_1476_ = l_Lean_binderPred_u2260___00__closed__1;
        leanh::lean_inc(v___x_1475_);
        v___x_1477_ = l_Lean_Syntax_isOfKind(v___x_1475_, v___x_1476_);
        if v___x_1477_ == 0 {
            let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1475_);
            leanh::lean_dec(v_x_1467_);
            v___x_1478_ = leanh::lean_box(1);
            v___x_1479_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1479_, 0, v___x_1478_);
            leanh::lean_ctor_set(v___x_1479_, 1, v_a_1469_);
            return v___x_1479_;
        } else {
            let mut v_ref_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1484_: u8 = 0;
            let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1480_ = leanh::lean_ctor_get(v_a_1468_, 5);
            v___x_1481_ = leanh::lean_unsigned_to_nat(1);
            v___x_1482_ = l_Lean_Syntax_getArg(v_x_1467_, v___x_1481_);
            leanh::lean_dec(v_x_1467_);
            v___x_1483_ = l_Lean_Syntax_getArg(v___x_1475_, v___x_1481_);
            leanh::lean_dec(v___x_1475_);
            v___x_1484_ = 0;
            v___x_1485_ = l_Lean_SourceInfo_fromRef(v_ref_1480_, v___x_1484_);
            v___x_1486_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__1;
            v___x_1487_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___closed__2;
            leanh::lean_inc(v___x_1485_);
            v___x_1488_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1488_, 0, v___x_1485_);
            leanh::lean_ctor_set(v___x_1488_, 1, v___x_1487_);
            v___x_1489_ = l_Lean_Syntax_node3(
                v___x_1485_,
                v___x_1486_,
                v___x_1482_,
                v___x_1488_,
                v___x_1483_,
            );
            v___x_1490_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1490_, 0, v___x_1489_);
            leanh::lean_ctor_set(v___x_1490_, 1, v_a_1469_);
            return v___x_1490_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5___boxed(
    mut v_x_1491_: *mut leanh::LeanObject,
    mut v_a_1492_: *mut leanh::LeanObject,
    mut v_a_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1494_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______5(v_x_1491_, v_a_1492_, v_a_1493_);
    leanh::lean_dec_ref(v_a_1492_);
    return v_res_1494_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6(
    mut v_x_1515_: *mut leanh::LeanObject,
    mut v_a_1516_: *mut leanh::LeanObject,
    mut v_a_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: u8 = 0;
    v___x_1518_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1515_);
    v___x_1519_ = l_Lean_Syntax_isOfKind(v_x_1515_, v___x_1518_);
    if v___x_1519_ == 0 {
        let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1515_);
        v___x_1520_ = leanh::lean_box(1);
        v___x_1521_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1521_, 0, v___x_1520_);
        leanh::lean_ctor_set(v___x_1521_, 1, v_a_1517_);
        return v___x_1521_;
    } else {
        let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: u8 = 0;
        v___x_1522_ = leanh::lean_unsigned_to_nat(2);
        v___x_1523_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1522_);
        v___x_1524_ = l_Lean_binderPred_u2208___00__closed__1;
        leanh::lean_inc(v___x_1523_);
        v___x_1525_ = l_Lean_Syntax_isOfKind(v___x_1523_, v___x_1524_);
        if v___x_1525_ == 0 {
            let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1523_);
            leanh::lean_dec(v_x_1515_);
            v___x_1526_ = leanh::lean_box(1);
            v___x_1527_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
            leanh::lean_ctor_set(v___x_1527_, 1, v_a_1517_);
            return v___x_1527_;
        } else {
            let mut v_ref_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1532_: u8 = 0;
            let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1528_ = leanh::lean_ctor_get(v_a_1516_, 5);
            v___x_1529_ = leanh::lean_unsigned_to_nat(1);
            v___x_1530_ = l_Lean_Syntax_getArg(v_x_1515_, v___x_1529_);
            leanh::lean_dec(v_x_1515_);
            v___x_1531_ = l_Lean_Syntax_getArg(v___x_1523_, v___x_1529_);
            leanh::lean_dec(v___x_1523_);
            v___x_1532_ = 0;
            v___x_1533_ = l_Lean_SourceInfo_fromRef(v_ref_1528_, v___x_1532_);
            v___x_1534_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__1;
            v___x_1535_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___closed__2;
            leanh::lean_inc(v___x_1533_);
            v___x_1536_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1536_, 0, v___x_1533_);
            leanh::lean_ctor_set(v___x_1536_, 1, v___x_1535_);
            v___x_1537_ = l_Lean_Syntax_node3(
                v___x_1533_,
                v___x_1534_,
                v___x_1530_,
                v___x_1536_,
                v___x_1531_,
            );
            v___x_1538_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1538_, 0, v___x_1537_);
            leanh::lean_ctor_set(v___x_1538_, 1, v_a_1517_);
            return v___x_1538_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6___boxed(
    mut v_x_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
    mut v_a_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______6(v_x_1539_, v_a_1540_, v_a_1541_);
    leanh::lean_dec_ref(v_a_1540_);
    return v_res_1542_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7(
    mut v_x_1563_: *mut leanh::LeanObject,
    mut v_a_1564_: *mut leanh::LeanObject,
    mut v_a_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    v___x_1566_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1563_);
    v___x_1567_ = l_Lean_Syntax_isOfKind(v_x_1563_, v___x_1566_);
    if v___x_1567_ == 0 {
        let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1563_);
        v___x_1568_ = leanh::lean_box(1);
        v___x_1569_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1569_, 0, v___x_1568_);
        leanh::lean_ctor_set(v___x_1569_, 1, v_a_1565_);
        return v___x_1569_;
    } else {
        let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: u8 = 0;
        v___x_1570_ = leanh::lean_unsigned_to_nat(2);
        v___x_1571_ = l_Lean_Syntax_getArg(v_x_1563_, v___x_1570_);
        v___x_1572_ = l_Lean_binderPred_u2209___00__closed__1;
        leanh::lean_inc(v___x_1571_);
        v___x_1573_ = l_Lean_Syntax_isOfKind(v___x_1571_, v___x_1572_);
        if v___x_1573_ == 0 {
            let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1571_);
            leanh::lean_dec(v_x_1563_);
            v___x_1574_ = leanh::lean_box(1);
            v___x_1575_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
            leanh::lean_ctor_set(v___x_1575_, 1, v_a_1565_);
            return v___x_1575_;
        } else {
            let mut v_ref_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1580_: u8 = 0;
            let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1576_ = leanh::lean_ctor_get(v_a_1564_, 5);
            v___x_1577_ = leanh::lean_unsigned_to_nat(1);
            v___x_1578_ = l_Lean_Syntax_getArg(v_x_1563_, v___x_1577_);
            leanh::lean_dec(v_x_1563_);
            v___x_1579_ = l_Lean_Syntax_getArg(v___x_1571_, v___x_1577_);
            leanh::lean_dec(v___x_1571_);
            v___x_1580_ = 0;
            v___x_1581_ = l_Lean_SourceInfo_fromRef(v_ref_1576_, v___x_1580_);
            v___x_1582_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__1;
            v___x_1583_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___closed__2;
            leanh::lean_inc(v___x_1581_);
            v___x_1584_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1584_, 0, v___x_1581_);
            leanh::lean_ctor_set(v___x_1584_, 1, v___x_1583_);
            v___x_1585_ = l_Lean_Syntax_node3(
                v___x_1581_,
                v___x_1582_,
                v___x_1578_,
                v___x_1584_,
                v___x_1579_,
            );
            v___x_1586_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
            leanh::lean_ctor_set(v___x_1586_, 1, v_a_1565_);
            return v___x_1586_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7___boxed(
    mut v_x_1587_: *mut leanh::LeanObject,
    mut v_a_1588_: *mut leanh::LeanObject,
    mut v_a_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______7(v_x_1587_, v_a_1588_, v_a_1589_);
    leanh::lean_dec_ref(v_a_1588_);
    return v_res_1590_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8(
    mut v_x_1611_: *mut leanh::LeanObject,
    mut v_a_1612_: *mut leanh::LeanObject,
    mut v_a_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: u8 = 0;
    v___x_1614_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1611_);
    v___x_1615_ = l_Lean_Syntax_isOfKind(v_x_1611_, v___x_1614_);
    if v___x_1615_ == 0 {
        let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1611_);
        v___x_1616_ = leanh::lean_box(1);
        v___x_1617_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1617_, 0, v___x_1616_);
        leanh::lean_ctor_set(v___x_1617_, 1, v_a_1613_);
        return v___x_1617_;
    } else {
        let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1621_: u8 = 0;
        v___x_1618_ = leanh::lean_unsigned_to_nat(2);
        v___x_1619_ = l_Lean_Syntax_getArg(v_x_1611_, v___x_1618_);
        v___x_1620_ = l_Lean_binderPred_u2286___00__closed__1;
        leanh::lean_inc(v___x_1619_);
        v___x_1621_ = l_Lean_Syntax_isOfKind(v___x_1619_, v___x_1620_);
        if v___x_1621_ == 0 {
            let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1619_);
            leanh::lean_dec(v_x_1611_);
            v___x_1622_ = leanh::lean_box(1);
            v___x_1623_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1623_, 0, v___x_1622_);
            leanh::lean_ctor_set(v___x_1623_, 1, v_a_1613_);
            return v___x_1623_;
        } else {
            let mut v_ref_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1628_: u8 = 0;
            let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1624_ = leanh::lean_ctor_get(v_a_1612_, 5);
            v___x_1625_ = leanh::lean_unsigned_to_nat(1);
            v___x_1626_ = l_Lean_Syntax_getArg(v_x_1611_, v___x_1625_);
            leanh::lean_dec(v_x_1611_);
            v___x_1627_ = l_Lean_Syntax_getArg(v___x_1619_, v___x_1625_);
            leanh::lean_dec(v___x_1619_);
            v___x_1628_ = 0;
            v___x_1629_ = l_Lean_SourceInfo_fromRef(v_ref_1624_, v___x_1628_);
            v___x_1630_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__1;
            v___x_1631_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___closed__2;
            leanh::lean_inc(v___x_1629_);
            v___x_1632_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1632_, 0, v___x_1629_);
            leanh::lean_ctor_set(v___x_1632_, 1, v___x_1631_);
            v___x_1633_ = l_Lean_Syntax_node3(
                v___x_1629_,
                v___x_1630_,
                v___x_1626_,
                v___x_1632_,
                v___x_1627_,
            );
            v___x_1634_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1634_, 0, v___x_1633_);
            leanh::lean_ctor_set(v___x_1634_, 1, v_a_1613_);
            return v___x_1634_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8___boxed(
    mut v_x_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______8(v_x_1635_, v_a_1636_, v_a_1637_);
    leanh::lean_dec_ref(v_a_1636_);
    return v_res_1638_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9(
    mut v_x_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
    mut v_a_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u8 = 0;
    v___x_1662_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1659_);
    v___x_1663_ = l_Lean_Syntax_isOfKind(v_x_1659_, v___x_1662_);
    if v___x_1663_ == 0 {
        let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1659_);
        v___x_1664_ = leanh::lean_box(1);
        v___x_1665_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1665_, 0, v___x_1664_);
        leanh::lean_ctor_set(v___x_1665_, 1, v_a_1661_);
        return v___x_1665_;
    } else {
        let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: u8 = 0;
        v___x_1666_ = leanh::lean_unsigned_to_nat(2);
        v___x_1667_ = l_Lean_Syntax_getArg(v_x_1659_, v___x_1666_);
        v___x_1668_ = l_Lean_binderPred_u2282___00__closed__1;
        leanh::lean_inc(v___x_1667_);
        v___x_1669_ = l_Lean_Syntax_isOfKind(v___x_1667_, v___x_1668_);
        if v___x_1669_ == 0 {
            let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1667_);
            leanh::lean_dec(v_x_1659_);
            v___x_1670_ = leanh::lean_box(1);
            v___x_1671_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1671_, 0, v___x_1670_);
            leanh::lean_ctor_set(v___x_1671_, 1, v_a_1661_);
            return v___x_1671_;
        } else {
            let mut v_ref_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1676_: u8 = 0;
            let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1672_ = leanh::lean_ctor_get(v_a_1660_, 5);
            v___x_1673_ = leanh::lean_unsigned_to_nat(1);
            v___x_1674_ = l_Lean_Syntax_getArg(v_x_1659_, v___x_1673_);
            leanh::lean_dec(v_x_1659_);
            v___x_1675_ = l_Lean_Syntax_getArg(v___x_1667_, v___x_1673_);
            leanh::lean_dec(v___x_1667_);
            v___x_1676_ = 0;
            v___x_1677_ = l_Lean_SourceInfo_fromRef(v_ref_1672_, v___x_1676_);
            v___x_1678_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__1;
            v___x_1679_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___closed__2;
            leanh::lean_inc(v___x_1677_);
            v___x_1680_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1680_, 0, v___x_1677_);
            leanh::lean_ctor_set(v___x_1680_, 1, v___x_1679_);
            v___x_1681_ = l_Lean_Syntax_node3(
                v___x_1677_,
                v___x_1678_,
                v___x_1674_,
                v___x_1680_,
                v___x_1675_,
            );
            v___x_1682_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1682_, 0, v___x_1681_);
            leanh::lean_ctor_set(v___x_1682_, 1, v_a_1661_);
            return v___x_1682_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9___boxed(
    mut v_x_1683_: *mut leanh::LeanObject,
    mut v_a_1684_: *mut leanh::LeanObject,
    mut v_a_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______9(v_x_1683_, v_a_1684_, v_a_1685_);
    leanh::lean_dec_ref(v_a_1684_);
    return v_res_1686_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10(
    mut v_x_1707_: *mut leanh::LeanObject,
    mut v_a_1708_: *mut leanh::LeanObject,
    mut v_a_1709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: u8 = 0;
    v___x_1710_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1707_);
    v___x_1711_ = l_Lean_Syntax_isOfKind(v_x_1707_, v___x_1710_);
    if v___x_1711_ == 0 {
        let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1707_);
        v___x_1712_ = leanh::lean_box(1);
        v___x_1713_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1713_, 0, v___x_1712_);
        leanh::lean_ctor_set(v___x_1713_, 1, v_a_1709_);
        return v___x_1713_;
    } else {
        let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1717_: u8 = 0;
        v___x_1714_ = leanh::lean_unsigned_to_nat(2);
        v___x_1715_ = l_Lean_Syntax_getArg(v_x_1707_, v___x_1714_);
        v___x_1716_ = l_Lean_binderPred_u2287___00__closed__1;
        leanh::lean_inc(v___x_1715_);
        v___x_1717_ = l_Lean_Syntax_isOfKind(v___x_1715_, v___x_1716_);
        if v___x_1717_ == 0 {
            let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1715_);
            leanh::lean_dec(v_x_1707_);
            v___x_1718_ = leanh::lean_box(1);
            v___x_1719_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1719_, 0, v___x_1718_);
            leanh::lean_ctor_set(v___x_1719_, 1, v_a_1709_);
            return v___x_1719_;
        } else {
            let mut v_ref_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1724_: u8 = 0;
            let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1720_ = leanh::lean_ctor_get(v_a_1708_, 5);
            v___x_1721_ = leanh::lean_unsigned_to_nat(1);
            v___x_1722_ = l_Lean_Syntax_getArg(v_x_1707_, v___x_1721_);
            leanh::lean_dec(v_x_1707_);
            v___x_1723_ = l_Lean_Syntax_getArg(v___x_1715_, v___x_1721_);
            leanh::lean_dec(v___x_1715_);
            v___x_1724_ = 0;
            v___x_1725_ = l_Lean_SourceInfo_fromRef(v_ref_1720_, v___x_1724_);
            v___x_1726_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__1;
            v___x_1727_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___closed__2;
            leanh::lean_inc(v___x_1725_);
            v___x_1728_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1728_, 0, v___x_1725_);
            leanh::lean_ctor_set(v___x_1728_, 1, v___x_1727_);
            v___x_1729_ = l_Lean_Syntax_node3(
                v___x_1725_,
                v___x_1726_,
                v___x_1722_,
                v___x_1728_,
                v___x_1723_,
            );
            v___x_1730_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1730_, 0, v___x_1729_);
            leanh::lean_ctor_set(v___x_1730_, 1, v_a_1709_);
            return v___x_1730_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10___boxed(
    mut v_x_1731_: *mut leanh::LeanObject,
    mut v_a_1732_: *mut leanh::LeanObject,
    mut v_a_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______10(v_x_1731_, v_a_1732_, v_a_1733_);
    leanh::lean_dec_ref(v_a_1732_);
    return v_res_1734_;
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11(
    mut v_x_1755_: *mut leanh::LeanObject,
    mut v_a_1756_: *mut leanh::LeanObject,
    mut v_a_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    v___x_1758_ = l_Lean_termSatisfies__binder__pred_x25_____00__closed__1;
    leanh::lean_inc(v_x_1755_);
    v___x_1759_ = l_Lean_Syntax_isOfKind(v_x_1755_, v___x_1758_);
    if v___x_1759_ == 0 {
        let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1755_);
        v___x_1760_ = leanh::lean_box(1);
        v___x_1761_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1761_, 0, v___x_1760_);
        leanh::lean_ctor_set(v___x_1761_, 1, v_a_1757_);
        return v___x_1761_;
    } else {
        let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: u8 = 0;
        v___x_1762_ = leanh::lean_unsigned_to_nat(2);
        v___x_1763_ = l_Lean_Syntax_getArg(v_x_1755_, v___x_1762_);
        v___x_1764_ = l_Lean_binderPred_u2283___00__closed__1;
        leanh::lean_inc(v___x_1763_);
        v___x_1765_ = l_Lean_Syntax_isOfKind(v___x_1763_, v___x_1764_);
        if v___x_1765_ == 0 {
            let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1763_);
            leanh::lean_dec(v_x_1755_);
            v___x_1766_ = leanh::lean_box(1);
            v___x_1767_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1767_, 0, v___x_1766_);
            leanh::lean_ctor_set(v___x_1767_, 1, v_a_1757_);
            return v___x_1767_;
        } else {
            let mut v_ref_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1772_: u8 = 0;
            let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_1768_ = leanh::lean_ctor_get(v_a_1756_, 5);
            v___x_1769_ = leanh::lean_unsigned_to_nat(1);
            v___x_1770_ = l_Lean_Syntax_getArg(v_x_1755_, v___x_1769_);
            leanh::lean_dec(v_x_1755_);
            v___x_1771_ = l_Lean_Syntax_getArg(v___x_1763_, v___x_1769_);
            leanh::lean_dec(v___x_1763_);
            v___x_1772_ = 0;
            v___x_1773_ = l_Lean_SourceInfo_fromRef(v_ref_1768_, v___x_1772_);
            v___x_1774_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__1;
            v___x_1775_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___closed__2;
            leanh::lean_inc(v___x_1773_);
            v___x_1776_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1776_, 0, v___x_1773_);
            leanh::lean_ctor_set(v___x_1776_, 1, v___x_1775_);
            v___x_1777_ = l_Lean_Syntax_node3(
                v___x_1773_,
                v___x_1774_,
                v___x_1770_,
                v___x_1776_,
                v___x_1771_,
            );
            v___x_1778_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
            leanh::lean_ctor_set(v___x_1778_, 1, v_a_1757_);
            return v___x_1778_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11___boxed(
    mut v_x_1779_: *mut leanh::LeanObject,
    mut v_a_1780_: *mut leanh::LeanObject,
    mut v_a_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Lean___aux__Init__BinderPredicates______macroRules__Lean__termSatisfies__binder__pred_x25______11(v_x_1779_, v_a_1780_, v_a_1781_);
    leanh::lean_dec_ref(v_a_1780_);
    return v_res_1782_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_BinderPredicates(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_BinderPredicates(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Parser_Category_binderPred = _init_l_Lean_Parser_Category_binderPred();
    leanh::lean_mark_persistent(l_Lean_Parser_Category_binderPred);
    l_Lean_term_u2203_____x2c__ = _init_l_Lean_term_u2203_____x2c__();
    leanh::lean_mark_persistent(l_Lean_term_u2203_____x2c__);
    l_Lean_term_u2200_____x2c__ = _init_l_Lean_term_u2200_____x2c__();
    leanh::lean_mark_persistent(l_Lean_term_u2200_____x2c__);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_BinderPredicates(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Meta_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_BinderPredicates(builtin);
}