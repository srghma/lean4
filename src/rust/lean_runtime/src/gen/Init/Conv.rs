// Lean compiler output
// Module: Init.Conv
// Imports: Init.Tactics Init.Meta
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Parser_Tactic_getConfigItems;
use crate::r#gen::Init::Meta::{initialize_Init_Meta, runtime_initialize_Init_Meta};
use crate::r#gen::Init::Notation::{l_Lean_Parser_Tactic_caseArg, l_Lean_binderIdent};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_discharger, l_Lean_Parser_Tactic_dsimpArgs,
    l_Lean_Parser_Tactic_optConfig, l_Lean_Parser_Tactic_rwRuleSeq, l_Lean_Parser_Tactic_simpArgs,
    l_Lean_Parser_Tactic_simpErase, l_Lean_Parser_Tactic_simpLemma, l_Lean_Parser_Tactic_simpStar,
    runtime_initialize_Init_Tactics,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::lean_array_push;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value: crate::leanh::LeanStringObject<
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value)
                as *mut crate::leanh::LeanObject,
            5855146430765573009 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 111, 110, 118, 0],
};
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
            as *mut crate::leanh::LeanObject,
        5852136541633594344 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value)
                as *mut crate::leanh::LeanObject,
            2853200300723924294 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [96, 40, 99, 111, 110, 118, 124, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
                as *mut crate::leanh::LeanObject,
            5852136541633594344 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_conv_quot: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Category_conv: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        99, 111, 110, 118, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value:
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
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value:
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
    m_data: [67, 111, 110, 118, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2194001538128159737 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        115, 101, 112, 66, 121, 49, 73, 110, 100, 101, 110, 116, 83, 101, 109, 105, 99, 111, 108,
        111, 110, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value)
            as *mut crate::leanh::LeanObject,
        12439213008700076310 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        99, 111, 110, 118, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4863285515324763763 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value:
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
    m_data: [123, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value:
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
        119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value)
            as *mut crate::leanh::LeanObject,
        1164644006045091397 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        115, 101, 112, 66, 121, 73, 110, 100, 101, 110, 116, 83, 101, 109, 105, 99, 111, 108, 111,
        110, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value)
            as *mut crate::leanh::LeanObject,
        8450841259565682059 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value:
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
    m_data: [125, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [99, 111, 110, 118, 83, 101, 113, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4619875164071285194 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value)
                as *mut crate::leanh::LeanObject,
            393173242845875278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convSeq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [111, 99, 99, 115, 87, 105, 108, 100, 99, 97, 114, 100, 0],
};
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11436923668760528595 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value:
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
    m_data: [42, 0],
};
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_occsWildcard: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value: crate::leanh::LeanStringObject<
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
    m_length: 11,
    m_data: [111, 99, 99, 115, 73, 110, 100, 101, 120, 101, 100, 0],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10410387794395025201 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [109, 97, 110, 121, 49, 0],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17243740965612849207 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 117, 109, 0],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value)
            as *mut crate::leanh::LeanObject,
        6110315075117401315 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_occsIndexed: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [111, 99, 99, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_occs___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3133829275317851260 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [97, 116, 111, 109, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            4024150434455327032 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__4_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__9_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__10_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__14_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [41, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__15_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__17_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_occs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
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
        119, 105, 116, 104, 65, 110, 110, 111, 116, 97, 116, 101, 83, 116, 97, 116, 101, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3238020878805402882 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        119, 105, 116, 104, 95, 97, 110, 110, 111, 116, 97, 116, 101, 95, 115, 116, 97, 116, 101,
        32, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value:
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
    m_data: [114, 97, 119, 83, 116, 120, 0],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value)
            as *mut crate::leanh::LeanObject,
        7922007774678457419 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value:
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
    m_data: [112, 112, 83, 112, 97, 99, 101, 0],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value)
            as *mut crate::leanh::LeanObject,
        17761616517784022991 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_withAnnotateState: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_skip___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 107, 105, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_skip___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_skip___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13842034534476526597 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_skip___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_skip___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_skip___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_skip___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_skip___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_skip: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_cbv___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [99, 98, 118, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_cbv___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12057338954073742905 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_cbv___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_cbv___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_cbv___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_cbv___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_cbv___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_cbv: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_lhs___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [108, 104, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_lhs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2383240203624611278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_lhs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_lhs___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_lhs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_lhs___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_lhs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_lhs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rhs___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [114, 104, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_rhs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14493188234565044157 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_rhs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rhs___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_rhs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rhs___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_rhs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_rhs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_fun___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [102, 117, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_fun___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_fun___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14856247777542608561 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_fun___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_fun___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_fun___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_fun___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_fun___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_fun: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_whnf___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [119, 104, 110, 102, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_whnf___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5293136351122059060 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_whnf___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_whnf___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_whnf___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_whnf___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_whnf___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_whnf: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_zeta___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [122, 101, 116, 97, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_zeta___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2162740105087520528 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_zeta___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_zeta___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_zeta___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_zeta___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_zeta___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_zeta: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_reduce___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [114, 101, 100, 117, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_reduce___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7650338142865358823 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_reduce___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_reduce___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_reduce___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_reduce___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_reduce___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_reduce: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_congr___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_congr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_congr___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14427030059196397072 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_congr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_congr___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_congr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_congr___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_congr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_congr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [97, 114, 103, 65, 114, 103, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9815751759067206459 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__2_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__4_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [64, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__7_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_argArg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [97, 114, 103, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_arg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_arg___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6940441580804063122 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_arg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [97, 114, 103, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_arg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_arg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_arg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_arg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_arg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [101, 120, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_ext___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5818266883322100681 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__3_value)
                as *mut crate::leanh::LeanObject,
            2302572775315350313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__5_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 111, 108, 71, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__5_value)
                as *mut crate::leanh::LeanObject,
            17597206043415342265 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_ext___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_ext___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_ext___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_ext___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_ext: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_change___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [99, 104, 97, 110, 103, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_change___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1203263152968118357 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [99, 104, 97, 110, 103, 101, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__4_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_change: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [100, 101, 108, 116, 97, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_delta___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8745909130110294463 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__3_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__3_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_delta: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [117, 110, 102, 111, 108, 100, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14363068710658641377 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_unfold: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 97, 116, 116, 101, 114, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3861856325106436923 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__2_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [112, 97, 116, 116, 101, 114, 110, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_pattern: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [114, 101, 119, 114, 105, 116, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value)
                as *mut crate::leanh::LeanObject,
            779923751473675077 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rewrite___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_rewrite: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_simp___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14621726445050439147 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [32, 111, 110, 108, 121, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__6_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__10_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [32, 91, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__14_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__15_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__16_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__20_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_simp: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
};
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4033974689118230740 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 105, 109, 112, 63, 0],
};
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpTrace___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_simpTrace: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [100, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value)
                as *mut crate::leanh::LeanObject,
            682381425026147175 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_dsimp___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_dsimp: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [100, 115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
};
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1408925737459485508 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [100, 115, 105, 109, 112, 63, 0],
};
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_dsimpTrace: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [115, 105, 109, 112, 77, 97, 116, 99, 104, 0],
};
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2709596213829771159 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [115, 105, 109, 112, 95, 109, 97, 116, 99, 104, 0],
};
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_simpMatch: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 108, 101, 97, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_clear___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12526317070040649423 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_clear: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        110, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 67, 111, 114, 101, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14672341133913102249 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 39, 0],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value:
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
    m_data: [32, 61, 62, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value:
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
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value)
            as *mut crate::leanh::LeanObject,
        11103865283154438669 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [110, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9934668988201376792 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_nestedTactic: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [99, 111, 110, 118, 84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3529167016356999086 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 110, 118, 39, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convTactic: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [110, 101, 115, 116, 101, 100, 67, 111, 110, 118, 0],
};
static mut l_Lean_Parser_Tactic_Conv_nestedConv___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13793888648781409952 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedConv___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedConv___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_nestedConv: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_paren___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_paren___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4160726102902615044 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_paren___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__4_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_paren___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_paren___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_paren___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_paren___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_paren___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_paren: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [99, 111, 110, 118, 82, 102, 108, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5675369482127682097 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [114, 102, 108, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convRfl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value) as *mut crate::leanh::LeanObject,3294379458557754569 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [99, 111, 110, 118, 68, 111, 110, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11329495071494069401 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [100, 111, 110, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convDone: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__2_value) as *mut crate::leanh::LeanObject,8876691400619696497 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value:
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
        99, 111, 110, 118, 84, 114, 97, 99, 101, 95, 115, 116, 97, 116, 101, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5453012680849693201 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value:
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
    m_data: [116, 114, 97, 99, 101, 95, 115, 116, 97, 116, 101, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convTrace__state: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 114, 97, 99, 101, 83, 116, 97, 116, 101, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value) as *mut crate::leanh::LeanObject,14912751384704677824 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [97, 108, 108, 71, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1113262671135127376 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_allGoals: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value) as *mut crate::leanh::LeanObject,14131640301685195369 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [97, 110, 121, 71, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17733550178357422433 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [97, 110, 121, 95, 103, 111, 97, 108, 115, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_anyGoals: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value) as *mut crate::leanh::LeanObject,2355218674864034728 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 110, 121, 95, 103, 111, 97, 108, 115, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [99, 97, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_case___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11752510286238259185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 97, 115, 101, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__4_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [124, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_case___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_case: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__0_value) as *mut crate::leanh::LeanObject,3714280620155270360 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 97, 115, 101, 39, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2260385614914559383 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [99, 97, 115, 101, 39, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case_x27___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_case_x27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value) as *mut crate::leanh::LeanObject,7640173075534255494 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [99, 111, 110, 118, 78, 101, 120, 116, 95, 95, 61, 62, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        3719486818457681805 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value:
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
    m_data: [110, 101, 120, 116, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject,13771926289831477797 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 65, 114, 103, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject,14546932361418667927 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [102, 111, 99, 117, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_focus___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_focus___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14932297365852547287 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_focus___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [102, 111, 99, 117, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_focus___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_focus___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_focus___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_focus___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_focus: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__0_value) as *mut crate::leanh::LeanObject,15976019963061198790 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value: crate::leanh::LeanStringObject<
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
    m_length: 11,
    m_data: [99, 111, 110, 118, 67, 111, 110, 118, 83, 101, 113, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18300610594507675016 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convConvSeq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 6,
    m_data: [99, 111, 110, 118, 194, 183, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        14887932109376590136 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 2,
    m_data: [194, 183, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value:
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
    m_data: [46, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 12,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_conv_xb7__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
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
        102, 97, 105, 108, 73, 102, 83, 117, 99, 99, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6792037844894501418 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        102, 97, 105, 108, 95, 105, 102, 95, 115, 117, 99, 99, 101, 115, 115, 32, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_failIfSuccess: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value) as *mut crate::leanh::LeanObject,17788448959859761123 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [102, 97, 105, 108, 95, 105, 102, 95, 115, 117, 99, 99, 101, 115, 115, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value:
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
    m_data: [99, 111, 110, 118, 82, 119, 95, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        1169967066955421272 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value:
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
    m_data: [114, 119, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_convRw____: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value:
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
    m_data: [99, 111, 110, 118, 69, 114, 119, 95, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        871072607707394147 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value:
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
    m_data: [101, 114, 119, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_convErw____: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value) as *mut crate::leanh::LeanObject,3488656302031949961 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value) as *mut crate::leanh::LeanObject,10138443044734372301 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value) as *mut crate::leanh::LeanObject,13577612981047608199 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value) as *mut crate::leanh::LeanObject,9886976150145685689 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value) as *mut crate::leanh::LeanObject,14183307858573822893 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value) as *mut crate::leanh::LeanObject,9666231177748665885 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value) as *mut crate::leanh::LeanObject,13340093926952294564 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value) as *mut crate::leanh::LeanObject,609174137020324014 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [99, 111, 110, 118, 65, 114, 103, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8815029478349537649 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [97, 114, 103, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convArgs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [99, 111, 110, 118, 76, 101, 102, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5744455334158526087 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [108, 101, 102, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convLeft: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__0_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [99, 111, 110, 118, 82, 105, 103, 104, 116, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10406812282498978092 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__2_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convRight: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [99, 111, 110, 118, 73, 110, 116, 114, 111, 95, 95, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        4938971775571215549 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value:
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
    m_data: [105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_convIntro______: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 110, 116, 101, 114, 80, 97, 116, 116, 101, 114, 110, 0],
};
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7552558446830534184 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value:
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
    m_data: [105, 110, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_enterPattern: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [101, 110, 116, 101, 114, 65, 114, 103, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7908174979996395449 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterArg___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_enterArg: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_enter___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [101, 110, 116, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_enter___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7814780372252873783 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enter___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enter___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_enter___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enter___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enter___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enter___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enter___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_enter: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value:
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
    m_data: [99, 111, 110, 118, 65, 112, 112, 108, 121, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        6570134606486243148 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value:
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
    m_data: [97, 112, 112, 108, 121, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convApply__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value) as *mut crate::leanh::LeanObject,5826123769708379594 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [102, 105, 114, 115, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_first___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17591797804533379362 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [102, 105, 114, 115, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__4_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [119, 105, 116, 104, 80, 111, 115, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__4_value)
                as *mut crate::leanh::LeanObject,
            17180264478054591478 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__6_value)
                as *mut crate::leanh::LeanObject,
            2214559063752339918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__8_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [112, 112, 68, 101, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__8_value)
                as *mut crate::leanh::LeanObject,
            2710995909225096690 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__10_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [112, 112, 76, 105, 110, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__10_value)
                as *mut crate::leanh::LeanObject,
            4227538229121138037 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__12_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__14_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 111, 108, 71, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__14_value)
                as *mut crate::leanh::LeanObject,
            4942254933594350711 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__16_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__17_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__18_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [124, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__20_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__21_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__20_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__22_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__23_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__24_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__25_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__26_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__25_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_first: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 110, 118, 84, 114, 121, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        15272911930721002417 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 121, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convTry__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value:
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
    m_data: [99, 111, 110, 118, 95, 60, 59, 62, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        2841688605323704715 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value:
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
    m_data: [32, 60, 59, 62, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value) as *mut crate::leanh::LeanObject,12695378809397736991 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__0_value) as *mut crate::leanh::LeanObject,8689124066155232629 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 59, 62, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value:
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
    m_data: [99, 111, 110, 118, 82, 101, 112, 101, 97, 116, 95, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        14131562680861795865 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value:
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
    m_data: [114, 101, 112, 101, 97, 116, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convRepeat__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 112, 101, 97, 116, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value: crate::leanh::LeanStringObject<
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
    m_length: 11,
    m_data: [101, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0],
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3123354491248406356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        101, 120, 116, 114, 97, 99, 116, 95, 108, 101, 116, 115, 32, 0,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value) as *mut crate::leanh::LeanObject,6287085762317100023 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__9_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_extractLets: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [108, 105, 102, 116, 76, 101, 116, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15211363250062378073 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [108, 105, 102, 116, 95, 108, 101, 116, 115, 32, 0],
};
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_liftLets___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_liftLets: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 116, 84, 111, 72, 97, 118, 101, 0],
};
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1576434579341158445 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value: crate::leanh::LeanStringObject<
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
    m_length: 11,
    m_data: [108, 101, 116, 95, 116, 111, 95, 104, 97, 118, 101, 0],
};
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_letToHave: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_conv___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
                as *mut crate::leanh::LeanObject,
            8265518440499324864 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 97, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__6_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 105, 110, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__14_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_conv: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [110, 111, 114, 109, 67, 97, 115, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2622230176999461939 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5411934985460699852 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__2_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 111, 114, 109, 95, 99, 97, 115, 116, 0],
};
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_normCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Parser_Category_conv() -> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2751_ = crate::leanh::lean_box(0);
    return v___x_2751_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Lean_binderIdent;
    v___x_3169_ = l_Lean_Parser_Tactic_Conv_ext___closed__8;
    v___x_3170_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3171_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3171_, 0, v___x_3170_);
    crate::leanh::lean_ctor_set(v___x_3171_, 1, v___x_3169_);
    crate::leanh::lean_ctor_set(v___x_3171_, 2, v___x_3168_);
    return v___x_3171_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3172_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__9,
    );
    v___x_3173_ = l_Lean_Parser_Tactic_Conv_ext___closed__4;
    v___x_3174_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3174_, 0, v___x_3173_);
    crate::leanh::lean_ctor_set(v___x_3174_, 1, v___x_3172_);
    return v___x_3174_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3175_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__10,
    );
    v___x_3176_ = l_Lean_Parser_Tactic_Conv_ext___closed__2;
    v___x_3177_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3178_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3178_, 0, v___x_3177_);
    crate::leanh::lean_ctor_set(v___x_3178_, 1, v___x_3176_);
    crate::leanh::lean_ctor_set(v___x_3178_, 2, v___x_3175_);
    return v___x_3178_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__11_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__11,
    );
    v___x_3180_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_3181_ = l_Lean_Parser_Tactic_Conv_ext___closed__1;
    v___x_3182_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3182_, 0, v___x_3181_);
    crate::leanh::lean_ctor_set(v___x_3182_, 1, v___x_3180_);
    crate::leanh::lean_ctor_set(v___x_3182_, 2, v___x_3179_);
    return v___x_3182_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext() -> *mut crate::leanh::LeanObject {
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3183_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__12_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__12,
    );
    return v___x_3183_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3297_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3298_ = l_Lean_Parser_Tactic_Conv_rewrite___closed__2;
    v___x_3299_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3300_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3300_, 0, v___x_3299_);
    crate::leanh::lean_ctor_set(v___x_3300_, 1, v___x_3298_);
    crate::leanh::lean_ctor_set(v___x_3300_, 2, v___x_3297_);
    return v___x_3300_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lean_Parser_Tactic_rwRuleSeq;
    v___x_3302_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__3_once),
        _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__3,
    );
    v___x_3303_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3304_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3304_, 0, v___x_3303_);
    crate::leanh::lean_ctor_set(v___x_3304_, 1, v___x_3302_);
    crate::leanh::lean_ctor_set(v___x_3304_, 2, v___x_3301_);
    return v___x_3304_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3305_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__4,
    );
    v___x_3306_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_3307_ = l_Lean_Parser_Tactic_Conv_rewrite___closed__1;
    v___x_3308_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3308_, 0, v___x_3307_);
    crate::leanh::lean_ctor_set(v___x_3308_, 1, v___x_3306_);
    crate::leanh::lean_ctor_set(v___x_3308_, 2, v___x_3305_);
    return v___x_3308_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_rewrite() -> *mut crate::leanh::LeanObject {
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3309_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__5,
    );
    return v___x_3309_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3321_ = l_Lean_Parser_Tactic_Conv_simp___closed__2;
    v___x_3322_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3323_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3323_, 0, v___x_3322_);
    crate::leanh::lean_ctor_set(v___x_3323_, 1, v___x_3321_);
    crate::leanh::lean_ctor_set(v___x_3323_, 2, v___x_3320_);
    return v___x_3323_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Lean_Parser_Tactic_discharger;
    v___x_3325_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3326_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3326_, 0, v___x_3325_);
    crate::leanh::lean_ctor_set(v___x_3326_, 1, v___x_3324_);
    return v___x_3326_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__4,
    );
    v___x_3328_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__3_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__3,
    );
    v___x_3329_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3330_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3330_, 0, v___x_3329_);
    crate::leanh::lean_ctor_set(v___x_3330_, 1, v___x_3328_);
    crate::leanh::lean_ctor_set(v___x_3330_, 2, v___x_3327_);
    return v___x_3330_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3338_ = l_Lean_Parser_Tactic_Conv_simp___closed__8;
    v___x_3339_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__5,
    );
    v___x_3340_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3341_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3341_, 0, v___x_3340_);
    crate::leanh::lean_ctor_set(v___x_3341_, 1, v___x_3339_);
    crate::leanh::lean_ctor_set(v___x_3341_, 2, v___x_3338_);
    return v___x_3341_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Lean_Parser_Tactic_simpLemma;
    v___x_3346_ = l_Lean_Parser_Tactic_simpErase;
    v___x_3347_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__3;
    v___x_3348_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3348_, 0, v___x_3347_);
    crate::leanh::lean_ctor_set(v___x_3348_, 1, v___x_3346_);
    crate::leanh::lean_ctor_set(v___x_3348_, 2, v___x_3345_);
    return v___x_3348_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3349_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__12_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__12,
    );
    v___x_3350_ = l_Lean_Parser_Tactic_simpStar;
    v___x_3351_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__3;
    v___x_3352_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3351_);
    crate::leanh::lean_ctor_set(v___x_3352_, 1, v___x_3350_);
    crate::leanh::lean_ctor_set(v___x_3352_, 2, v___x_3349_);
    return v___x_3352_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_3357_: u8 = 0;
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3357_ = 0;
    v___x_3358_ = l_Lean_Parser_Tactic_Conv_simp___closed__16;
    v___x_3359_ = l_Lean_Parser_Tactic_Conv_simp___closed__14;
    v___x_3360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__13_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__13,
    );
    v___x_3361_ = crate::leanh::lean_alloc_ctor(10, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3361_, 0, v___x_3360_);
    crate::leanh::lean_ctor_set(v___x_3361_, 1, v___x_3359_);
    crate::leanh::lean_ctor_set(v___x_3361_, 2, v___x_3358_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3361_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_3357_,
    );
    return v___x_3361_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3362_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__17_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__17,
    );
    v___x_3363_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5;
    v___x_3364_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3364_, 0, v___x_3363_);
    crate::leanh::lean_ctor_set(v___x_3364_, 1, v___x_3362_);
    return v___x_3364_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3365_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__18_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__18,
    );
    v___x_3366_ = l_Lean_Parser_Tactic_Conv_simp___closed__11;
    v___x_3367_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3368_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3368_, 0, v___x_3367_);
    crate::leanh::lean_ctor_set(v___x_3368_, 1, v___x_3366_);
    crate::leanh::lean_ctor_set(v___x_3368_, 2, v___x_3365_);
    return v___x_3368_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3372_ = l_Lean_Parser_Tactic_Conv_simp___closed__21;
    v___x_3373_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__19_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__19,
    );
    v___x_3374_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3375_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3375_, 0, v___x_3374_);
    crate::leanh::lean_ctor_set(v___x_3375_, 1, v___x_3373_);
    crate::leanh::lean_ctor_set(v___x_3375_, 2, v___x_3372_);
    return v___x_3375_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3376_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__22_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__22,
    );
    v___x_3377_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3378_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3378_, 0, v___x_3377_);
    crate::leanh::lean_ctor_set(v___x_3378_, 1, v___x_3376_);
    return v___x_3378_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3379_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__23_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__23,
    );
    v___x_3380_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__9,
    );
    v___x_3381_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3382_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3382_, 0, v___x_3381_);
    crate::leanh::lean_ctor_set(v___x_3382_, 1, v___x_3380_);
    crate::leanh::lean_ctor_set(v___x_3382_, 2, v___x_3379_);
    return v___x_3382_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3383_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__24_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__24,
    );
    v___x_3384_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_3385_ = l_Lean_Parser_Tactic_Conv_simp___closed__1;
    v___x_3386_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3386_, 0, v___x_3385_);
    crate::leanh::lean_ctor_set(v___x_3386_, 1, v___x_3384_);
    crate::leanh::lean_ctor_set(v___x_3386_, 2, v___x_3383_);
    return v___x_3386_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp() -> *mut crate::leanh::LeanObject {
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3387_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__25_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__25,
    );
    return v___x_3387_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3400_ = l_Lean_Parser_Tactic_Conv_simpTrace___closed__3;
    v___x_3401_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3402_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3402_, 0, v___x_3401_);
    crate::leanh::lean_ctor_set(v___x_3402_, 1, v___x_3400_);
    crate::leanh::lean_ctor_set(v___x_3402_, 2, v___x_3399_);
    return v___x_3402_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3403_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__4,
    );
    v___x_3404_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__4,
    );
    v___x_3405_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3406_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3406_, 0, v___x_3405_);
    crate::leanh::lean_ctor_set(v___x_3406_, 1, v___x_3404_);
    crate::leanh::lean_ctor_set(v___x_3406_, 2, v___x_3403_);
    return v___x_3406_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_Parser_Tactic_Conv_simp___closed__8;
    v___x_3408_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__5,
    );
    v___x_3409_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3410_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3410_, 0, v___x_3409_);
    crate::leanh::lean_ctor_set(v___x_3410_, 1, v___x_3408_);
    crate::leanh::lean_ctor_set(v___x_3410_, 2, v___x_3407_);
    return v___x_3410_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3411_ = l_Lean_Parser_Tactic_simpArgs;
    v___x_3412_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3413_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3413_, 0, v___x_3412_);
    crate::leanh::lean_ctor_set(v___x_3413_, 1, v___x_3411_);
    return v___x_3413_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__7,
    );
    v___x_3415_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__6,
    );
    v___x_3416_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3417_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3417_, 0, v___x_3416_);
    crate::leanh::lean_ctor_set(v___x_3417_, 1, v___x_3415_);
    crate::leanh::lean_ctor_set(v___x_3417_, 2, v___x_3414_);
    return v___x_3417_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__8,
    );
    v___x_3419_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_3420_ = l_Lean_Parser_Tactic_Conv_simpTrace___closed__1;
    v___x_3421_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3421_, 0, v___x_3420_);
    crate::leanh::lean_ctor_set(v___x_3421_, 1, v___x_3419_);
    crate::leanh::lean_ctor_set(v___x_3421_, 2, v___x_3418_);
    return v___x_3421_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace() -> *mut crate::leanh::LeanObject {
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3422_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__9,
    );
    return v___x_3422_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3434_ = l_Lean_Parser_Tactic_Conv_dsimp___closed__2;
    v___x_3435_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3436_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3436_, 0, v___x_3435_);
    crate::leanh::lean_ctor_set(v___x_3436_, 1, v___x_3434_);
    crate::leanh::lean_ctor_set(v___x_3436_, 2, v___x_3433_);
    return v___x_3436_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__4,
    );
    v___x_3438_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__3_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__3,
    );
    v___x_3439_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3440_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3440_, 0, v___x_3439_);
    crate::leanh::lean_ctor_set(v___x_3440_, 1, v___x_3438_);
    crate::leanh::lean_ctor_set(v___x_3440_, 2, v___x_3437_);
    return v___x_3440_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ = l_Lean_Parser_Tactic_Conv_simp___closed__8;
    v___x_3442_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__4,
    );
    v___x_3443_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3444_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3444_, 0, v___x_3443_);
    crate::leanh::lean_ctor_set(v___x_3444_, 1, v___x_3442_);
    crate::leanh::lean_ctor_set(v___x_3444_, 2, v___x_3441_);
    return v___x_3444_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3445_: u8 = 0;
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3445_ = 0;
    v___x_3446_ = l_Lean_Parser_Tactic_Conv_simp___closed__16;
    v___x_3447_ = l_Lean_Parser_Tactic_Conv_simp___closed__14;
    v___x_3448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__12_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__12,
    );
    v___x_3449_ = crate::leanh::lean_alloc_ctor(10, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3449_, 0, v___x_3448_);
    crate::leanh::lean_ctor_set(v___x_3449_, 1, v___x_3447_);
    crate::leanh::lean_ctor_set(v___x_3449_, 2, v___x_3446_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3449_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_3445_,
    );
    return v___x_3449_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__6,
    );
    v___x_3451_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5;
    v___x_3452_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3452_, 0, v___x_3451_);
    crate::leanh::lean_ctor_set(v___x_3452_, 1, v___x_3450_);
    return v___x_3452_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__7,
    );
    v___x_3454_ = l_Lean_Parser_Tactic_Conv_simp___closed__11;
    v___x_3455_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3456_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3456_, 0, v___x_3455_);
    crate::leanh::lean_ctor_set(v___x_3456_, 1, v___x_3454_);
    crate::leanh::lean_ctor_set(v___x_3456_, 2, v___x_3453_);
    return v___x_3456_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3457_ = l_Lean_Parser_Tactic_Conv_simp___closed__21;
    v___x_3458_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__8,
    );
    v___x_3459_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3460_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3460_, 0, v___x_3459_);
    crate::leanh::lean_ctor_set(v___x_3460_, 1, v___x_3458_);
    crate::leanh::lean_ctor_set(v___x_3460_, 2, v___x_3457_);
    return v___x_3460_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__9,
    );
    v___x_3462_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3463_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3463_, 0, v___x_3462_);
    crate::leanh::lean_ctor_set(v___x_3463_, 1, v___x_3461_);
    return v___x_3463_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__10,
    );
    v___x_3465_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__5,
    );
    v___x_3466_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3467_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3467_, 0, v___x_3466_);
    crate::leanh::lean_ctor_set(v___x_3467_, 1, v___x_3465_);
    crate::leanh::lean_ctor_set(v___x_3467_, 2, v___x_3464_);
    return v___x_3467_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3468_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__11_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__11,
    );
    v___x_3469_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_3470_ = l_Lean_Parser_Tactic_Conv_dsimp___closed__1;
    v___x_3471_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3471_, 0, v___x_3470_);
    crate::leanh::lean_ctor_set(v___x_3471_, 1, v___x_3469_);
    crate::leanh::lean_ctor_set(v___x_3471_, 2, v___x_3468_);
    return v___x_3471_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp() -> *mut crate::leanh::LeanObject {
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__12_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__12,
    );
    return v___x_3472_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3484_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3485_ = l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3;
    v___x_3486_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3487_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3487_, 0, v___x_3486_);
    crate::leanh::lean_ctor_set(v___x_3487_, 1, v___x_3485_);
    crate::leanh::lean_ctor_set(v___x_3487_, 2, v___x_3484_);
    return v___x_3487_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3488_ = l_Lean_Parser_Tactic_Conv_simp___closed__8;
    v___x_3489_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4,
    );
    v___x_3490_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3491_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3491_, 0, v___x_3490_);
    crate::leanh::lean_ctor_set(v___x_3491_, 1, v___x_3489_);
    crate::leanh::lean_ctor_set(v___x_3491_, 2, v___x_3488_);
    return v___x_3491_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = l_Lean_Parser_Tactic_dsimpArgs;
    v___x_3493_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3494_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3494_, 0, v___x_3493_);
    crate::leanh::lean_ctor_set(v___x_3494_, 1, v___x_3492_);
    return v___x_3494_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3495_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6,
    );
    v___x_3496_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5,
    );
    v___x_3497_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3498_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3498_, 0, v___x_3497_);
    crate::leanh::lean_ctor_set(v___x_3498_, 1, v___x_3496_);
    crate::leanh::lean_ctor_set(v___x_3498_, 2, v___x_3495_);
    return v___x_3498_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3499_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7,
    );
    v___x_3500_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_3501_ = l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1;
    v___x_3502_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3502_, 0, v___x_3501_);
    crate::leanh::lean_ctor_set(v___x_3502_, 1, v___x_3500_);
    crate::leanh::lean_ctor_set(v___x_3502_, 2, v___x_3499_);
    return v___x_3502_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace() -> *mut crate::leanh::LeanObject {
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3503_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8,
    );
    return v___x_3503_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1(
    mut v_x_3704_: *mut crate::leanh::LeanObject,
    mut v_a_3705_: *mut crate::leanh::LeanObject,
    mut v_a_3706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u8 = 0;
    v___x_3707_ = l_Lean_Parser_Tactic_Conv_convRfl___closed__1;
    v___x_3708_ = l_Lean_Syntax_isOfKind(v_x_3704_, v___x_3707_);
    if v___x_3708_ == 0 {
        let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3709_ = crate::leanh::lean_box(1);
        v___x_3710_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3710_, 0, v___x_3709_);
        crate::leanh::lean_ctor_set(v___x_3710_, 1, v_a_3706_);
        return v___x_3710_;
    } else {
        let mut v_ref_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3712_: u8 = 0;
        let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_3711_ = crate::leanh::lean_ctor_get(v_a_3705_, 5);
        v___x_3712_ = 0;
        v___x_3713_ = l_Lean_SourceInfo_fromRef(v_ref_3711_, v___x_3712_);
        v___x_3714_ = l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1;
        v___x_3715_ = l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2;
        crate::leanh::lean_inc_n(v___x_3713_, 7);
        v___x_3716_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3716_, 0, v___x_3713_);
        crate::leanh::lean_ctor_set(v___x_3716_, 1, v___x_3715_);
        v___x_3717_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3718_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3713_);
        crate::leanh::lean_ctor_set(v___x_3718_, 1, v___x_3717_);
        v___x_3719_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3720_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3721_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3722_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7;
        v___x_3723_ = l_Lean_Parser_Tactic_Conv_convRfl___closed__2;
        v___x_3724_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3724_, 0, v___x_3713_);
        crate::leanh::lean_ctor_set(v___x_3724_, 1, v___x_3723_);
        v___x_3725_ = l_Lean_Syntax_node1(v___x_3713_, v___x_3722_, v___x_3724_);
        v___x_3726_ = l_Lean_Syntax_node1(v___x_3713_, v___x_3721_, v___x_3725_);
        v___x_3727_ = l_Lean_Syntax_node1(v___x_3713_, v___x_3720_, v___x_3726_);
        v___x_3728_ = l_Lean_Syntax_node1(v___x_3713_, v___x_3719_, v___x_3727_);
        v___x_3729_ = l_Lean_Syntax_node3(
            v___x_3713_,
            v___x_3714_,
            v___x_3716_,
            v___x_3718_,
            v___x_3728_,
        );
        v___x_3730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3730_, 0, v___x_3729_);
        crate::leanh::lean_ctor_set(v___x_3730_, 1, v_a_3706_);
        return v___x_3730_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___boxed(
    mut v_x_3731_: *mut crate::leanh::LeanObject,
    mut v_a_3732_: *mut crate::leanh::LeanObject,
    mut v_a_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3734_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1(v_x_3731_, v_a_3732_, v_a_3733_);
    crate::leanh::lean_dec_ref(v_a_3732_);
    return v_res_3734_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1(
    mut v_x_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
    mut v_a_3758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    v___x_3759_ = l_Lean_Parser_Tactic_Conv_convDone___closed__1;
    v___x_3760_ = l_Lean_Syntax_isOfKind(v_x_3756_, v___x_3759_);
    if v___x_3760_ == 0 {
        let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3761_ = crate::leanh::lean_box(1);
        v___x_3762_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3762_, 0, v___x_3761_);
        crate::leanh::lean_ctor_set(v___x_3762_, 1, v_a_3758_);
        return v___x_3762_;
    } else {
        let mut v_ref_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3764_: u8 = 0;
        let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_3763_ = crate::leanh::lean_ctor_get(v_a_3757_, 5);
        v___x_3764_ = 0;
        v___x_3765_ = l_Lean_SourceInfo_fromRef(v_ref_3763_, v___x_3764_);
        v___x_3766_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_3767_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_3765_, 7);
        v___x_3768_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3768_, 0, v___x_3765_);
        crate::leanh::lean_ctor_set(v___x_3768_, 1, v___x_3767_);
        v___x_3769_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3770_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3770_, 0, v___x_3765_);
        crate::leanh::lean_ctor_set(v___x_3770_, 1, v___x_3769_);
        v___x_3771_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3772_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3773_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3774_ = l_Lean_Parser_Tactic_Conv_convDone___closed__2;
        v___x_3775_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0;
        v___x_3776_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3776_, 0, v___x_3765_);
        crate::leanh::lean_ctor_set(v___x_3776_, 1, v___x_3774_);
        v___x_3777_ = l_Lean_Syntax_node1(v___x_3765_, v___x_3775_, v___x_3776_);
        v___x_3778_ = l_Lean_Syntax_node1(v___x_3765_, v___x_3773_, v___x_3777_);
        v___x_3779_ = l_Lean_Syntax_node1(v___x_3765_, v___x_3772_, v___x_3778_);
        v___x_3780_ = l_Lean_Syntax_node1(v___x_3765_, v___x_3771_, v___x_3779_);
        v___x_3781_ = l_Lean_Syntax_node3(
            v___x_3765_,
            v___x_3766_,
            v___x_3768_,
            v___x_3770_,
            v___x_3780_,
        );
        v___x_3782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3782_, 0, v___x_3781_);
        crate::leanh::lean_ctor_set(v___x_3782_, 1, v_a_3758_);
        return v___x_3782_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___boxed(
    mut v_x_3783_: *mut crate::leanh::LeanObject,
    mut v_a_3784_: *mut crate::leanh::LeanObject,
    mut v_a_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3786_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1(v_x_3783_, v_a_3784_, v_a_3785_);
    crate::leanh::lean_dec_ref(v_a_3784_);
    return v_res_3786_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1(
    mut v_x_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: u8 = 0;
    v___x_3812_ = l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1;
    v___x_3813_ = l_Lean_Syntax_isOfKind(v_x_3809_, v___x_3812_);
    if v___x_3813_ == 0 {
        let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3814_ = crate::leanh::lean_box(1);
        v___x_3815_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3814_);
        crate::leanh::lean_ctor_set(v___x_3815_, 1, v_a_3811_);
        return v___x_3815_;
    } else {
        let mut v_ref_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3817_: u8 = 0;
        let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_3816_ = crate::leanh::lean_ctor_get(v_a_3810_, 5);
        v___x_3817_ = 0;
        v___x_3818_ = l_Lean_SourceInfo_fromRef(v_ref_3816_, v___x_3817_);
        v___x_3819_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_3820_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_3818_, 7);
        v___x_3821_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3821_, 0, v___x_3818_);
        crate::leanh::lean_ctor_set(v___x_3821_, 1, v___x_3820_);
        v___x_3822_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3823_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3823_, 0, v___x_3818_);
        crate::leanh::lean_ctor_set(v___x_3823_, 1, v___x_3822_);
        v___x_3824_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3825_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3826_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3827_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1;
        v___x_3828_ = l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2;
        v___x_3829_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3818_);
        crate::leanh::lean_ctor_set(v___x_3829_, 1, v___x_3828_);
        v___x_3830_ = l_Lean_Syntax_node1(v___x_3818_, v___x_3827_, v___x_3829_);
        v___x_3831_ = l_Lean_Syntax_node1(v___x_3818_, v___x_3826_, v___x_3830_);
        v___x_3832_ = l_Lean_Syntax_node1(v___x_3818_, v___x_3825_, v___x_3831_);
        v___x_3833_ = l_Lean_Syntax_node1(v___x_3818_, v___x_3824_, v___x_3832_);
        v___x_3834_ = l_Lean_Syntax_node3(
            v___x_3818_,
            v___x_3819_,
            v___x_3821_,
            v___x_3823_,
            v___x_3833_,
        );
        v___x_3835_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3835_, 0, v___x_3834_);
        crate::leanh::lean_ctor_set(v___x_3835_, 1, v_a_3811_);
        return v___x_3835_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___boxed(
    mut v_x_3836_: *mut crate::leanh::LeanObject,
    mut v_a_3837_: *mut crate::leanh::LeanObject,
    mut v_a_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1(v_x_3836_, v_a_3837_, v_a_3838_);
    crate::leanh::lean_dec_ref(v_a_3837_);
    return v_res_3839_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1(
    mut v_x_3866_: *mut crate::leanh::LeanObject,
    mut v_a_3867_: *mut crate::leanh::LeanObject,
    mut v_a_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: u8 = 0;
    v___x_3869_ = l_Lean_Parser_Tactic_Conv_allGoals___closed__1;
    crate::leanh::lean_inc(v_x_3866_);
    v___x_3870_ = l_Lean_Syntax_isOfKind(v_x_3866_, v___x_3869_);
    if v___x_3870_ == 0 {
        let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3866_);
        v___x_3871_ = crate::leanh::lean_box(1);
        v___x_3872_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3872_, 0, v___x_3871_);
        crate::leanh::lean_ctor_set(v___x_3872_, 1, v_a_3868_);
        return v___x_3872_;
    } else {
        let mut v_ref_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3878_: u8 = 0;
        let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_3873_ = crate::leanh::lean_ctor_get(v_a_3867_, 5);
        v___x_3874_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_3875_ = l_Lean_Syntax_getArg(v_x_3866_, v___x_3874_);
        v___x_3876_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3877_ = l_Lean_Syntax_getArg(v_x_3866_, v___x_3876_);
        crate::leanh::lean_dec(v_x_3866_);
        v___x_3878_ = 0;
        v___x_3879_ = l_Lean_SourceInfo_fromRef(v_ref_3873_, v___x_3878_);
        v___x_3880_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_3881_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_3879_, 11);
        v___x_3882_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3879_);
        crate::leanh::lean_ctor_set(v___x_3882_, 1, v___x_3881_);
        v___x_3883_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3884_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3884_, 0, v___x_3879_);
        crate::leanh::lean_ctor_set(v___x_3884_, 1, v___x_3883_);
        v___x_3885_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3886_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3887_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3888_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0;
        v___x_3889_ = l_Lean_SourceInfo_fromRef(v_tk_3875_, v___x_3870_);
        crate::leanh::lean_dec(v_tk_3875_);
        v___x_3890_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1;
        v___x_3891_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3891_, 0, v___x_3889_);
        crate::leanh::lean_ctor_set(v___x_3891_, 1, v___x_3890_);
        v___x_3892_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_3893_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_3894_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3894_, 0, v___x_3879_);
        crate::leanh::lean_ctor_set(v___x_3894_, 1, v___x_3893_);
        crate::leanh::lean_inc_ref(v___x_3884_);
        v___x_3895_ = l_Lean_Syntax_node3(
            v___x_3879_,
            v___x_3892_,
            v___x_3894_,
            v___x_3884_,
            v___x_3877_,
        );
        v___x_3896_ = l_Lean_Syntax_node1(v___x_3879_, v___x_3887_, v___x_3895_);
        v___x_3897_ = l_Lean_Syntax_node1(v___x_3879_, v___x_3886_, v___x_3896_);
        v___x_3898_ = l_Lean_Syntax_node1(v___x_3879_, v___x_3885_, v___x_3897_);
        v___x_3899_ = l_Lean_Syntax_node2(v___x_3879_, v___x_3888_, v___x_3891_, v___x_3898_);
        v___x_3900_ = l_Lean_Syntax_node1(v___x_3879_, v___x_3887_, v___x_3899_);
        v___x_3901_ = l_Lean_Syntax_node1(v___x_3879_, v___x_3886_, v___x_3900_);
        v___x_3902_ = l_Lean_Syntax_node1(v___x_3879_, v___x_3885_, v___x_3901_);
        v___x_3903_ = l_Lean_Syntax_node3(
            v___x_3879_,
            v___x_3880_,
            v___x_3882_,
            v___x_3884_,
            v___x_3902_,
        );
        v___x_3904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3904_, 0, v___x_3903_);
        crate::leanh::lean_ctor_set(v___x_3904_, 1, v_a_3868_);
        return v___x_3904_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___boxed(
    mut v_x_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v_a_3907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3908_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1(v_x_3905_, v_a_3906_, v_a_3907_);
    crate::leanh::lean_dec_ref(v_a_3906_);
    return v_res_3908_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1(
    mut v_x_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    v___x_3938_ = l_Lean_Parser_Tactic_Conv_anyGoals___closed__1;
    crate::leanh::lean_inc(v_x_3935_);
    v___x_3939_ = l_Lean_Syntax_isOfKind(v_x_3935_, v___x_3938_);
    if v___x_3939_ == 0 {
        let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3935_);
        v___x_3940_ = crate::leanh::lean_box(1);
        v___x_3941_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3941_, 0, v___x_3940_);
        crate::leanh::lean_ctor_set(v___x_3941_, 1, v_a_3937_);
        return v___x_3941_;
    } else {
        let mut v_ref_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3947_: u8 = 0;
        let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        v_ref_3942_ = crate::leanh::lean_ctor_get(v_a_3936_, 5);
        v___x_3943_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_3944_ = l_Lean_Syntax_getArg(v_x_3935_, v___x_3943_);
        v___x_3945_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3946_ = l_Lean_Syntax_getArg(v_x_3935_, v___x_3945_);
        crate::leanh::lean_dec(v_x_3935_);
        v___x_3947_ = 0;
        v___x_3948_ = l_Lean_SourceInfo_fromRef(v_ref_3942_, v___x_3947_);
        v___x_3949_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_3950_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_3948_, 11);
        v___x_3951_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3951_, 0, v___x_3948_);
        crate::leanh::lean_ctor_set(v___x_3951_, 1, v___x_3950_);
        v___x_3952_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3953_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3953_, 0, v___x_3948_);
        crate::leanh::lean_ctor_set(v___x_3953_, 1, v___x_3952_);
        v___x_3954_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3955_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3956_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3957_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0;
        v___x_3958_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3939_);
        crate::leanh::lean_dec(v_tk_3944_);
        v___x_3959_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1;
        v___x_3960_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3960_, 0, v___x_3958_);
        crate::leanh::lean_ctor_set(v___x_3960_, 1, v___x_3959_);
        v___x_3961_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_3962_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_3963_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3963_, 0, v___x_3948_);
        crate::leanh::lean_ctor_set(v___x_3963_, 1, v___x_3962_);
        crate::leanh::lean_inc_ref(v___x_3953_);
        v___x_3964_ = l_Lean_Syntax_node3(
            v___x_3948_,
            v___x_3961_,
            v___x_3963_,
            v___x_3953_,
            v___x_3946_,
        );
        v___x_3965_ = l_Lean_Syntax_node1(v___x_3948_, v___x_3956_, v___x_3964_);
        v___x_3966_ = l_Lean_Syntax_node1(v___x_3948_, v___x_3955_, v___x_3965_);
        v___x_3967_ = l_Lean_Syntax_node1(v___x_3948_, v___x_3954_, v___x_3966_);
        v___x_3968_ = l_Lean_Syntax_node2(v___x_3948_, v___x_3957_, v___x_3960_, v___x_3967_);
        v___x_3969_ = l_Lean_Syntax_node1(v___x_3948_, v___x_3956_, v___x_3968_);
        v___x_3970_ = l_Lean_Syntax_node1(v___x_3948_, v___x_3955_, v___x_3969_);
        v___x_3971_ = l_Lean_Syntax_node1(v___x_3948_, v___x_3954_, v___x_3970_);
        v___x_3972_ = l_Lean_Syntax_node3(
            v___x_3948_,
            v___x_3949_,
            v___x_3951_,
            v___x_3953_,
            v___x_3971_,
        );
        v___x_3973_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3973_, 0, v___x_3972_);
        crate::leanh::lean_ctor_set(v___x_3973_, 1, v_a_3937_);
        return v___x_3973_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___boxed(
    mut v_x_3974_: *mut crate::leanh::LeanObject,
    mut v_a_3975_: *mut crate::leanh::LeanObject,
    mut v_a_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3977_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1(v_x_3974_, v_a_3975_, v_a_3976_);
    crate::leanh::lean_dec_ref(v_a_3975_);
    return v_res_3977_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3992_ = 0;
    v___x_3993_ = l_Lean_Parser_Tactic_Conv_case___closed__5;
    v___x_3994_ = l_Lean_Parser_Tactic_Conv_case___closed__4;
    v___x_3995_ = l_Lean_Parser_Tactic_caseArg;
    v___x_3996_ = crate::leanh::lean_alloc_ctor(11, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3996_, 0, v___x_3995_);
    crate::leanh::lean_ctor_set(v___x_3996_, 1, v___x_3994_);
    crate::leanh::lean_ctor_set(v___x_3996_, 2, v___x_3993_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3996_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_3992_,
    );
    return v___x_3996_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3997_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__6,
    );
    v___x_3998_ = l_Lean_Parser_Tactic_Conv_case___closed__3;
    v___x_3999_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4000_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4000_, 0, v___x_3999_);
    crate::leanh::lean_ctor_set(v___x_4000_, 1, v___x_3998_);
    crate::leanh::lean_ctor_set(v___x_4000_, 2, v___x_3997_);
    return v___x_4000_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4001_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5;
    v___x_4002_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__7,
    );
    v___x_4003_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4004_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4004_, 0, v___x_4003_);
    crate::leanh::lean_ctor_set(v___x_4004_, 1, v___x_4002_);
    crate::leanh::lean_ctor_set(v___x_4004_, 2, v___x_4001_);
    return v___x_4004_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4005_ = l_Lean_Parser_Tactic_Conv_convSeq;
    v___x_4006_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__8,
    );
    v___x_4007_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4008_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4008_, 0, v___x_4007_);
    crate::leanh::lean_ctor_set(v___x_4008_, 1, v___x_4006_);
    crate::leanh::lean_ctor_set(v___x_4008_, 2, v___x_4005_);
    return v___x_4008_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4009_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__9,
    );
    v___x_4010_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_4011_ = l_Lean_Parser_Tactic_Conv_case___closed__1;
    v___x_4012_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4012_, 0, v___x_4011_);
    crate::leanh::lean_ctor_set(v___x_4012_, 1, v___x_4010_);
    crate::leanh::lean_ctor_set(v___x_4012_, 2, v___x_4009_);
    return v___x_4012_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case() -> *mut crate::leanh::LeanObject {
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4013_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__10,
    );
    return v___x_4013_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4019_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_4019_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1(
    mut v_x_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
    mut v_a_4023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: u8 = 0;
    v___x_4024_ = l_Lean_Parser_Tactic_Conv_case___closed__0;
    v___x_4025_ = l_Lean_Parser_Tactic_Conv_case___closed__1;
    crate::leanh::lean_inc(v_x_4021_);
    v___x_4026_ = l_Lean_Syntax_isOfKind(v_x_4021_, v___x_4025_);
    if v___x_4026_ == 0 {
        let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4021_);
        v___x_4027_ = crate::leanh::lean_box(1);
        v___x_4028_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4028_, 0, v___x_4027_);
        crate::leanh::lean_ctor_set(v___x_4028_, 1, v_a_4023_);
        return v___x_4028_;
    } else {
        let mut v_ref_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_arr_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4040_: u8 = 0;
        let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4029_ = crate::leanh::lean_ctor_get(v_a_4022_, 5);
        v___x_4030_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_4031_ = l_Lean_Syntax_getArg(v_x_4021_, v___x_4030_);
        v___x_4032_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4033_ = l_Lean_Syntax_getArg(v_x_4021_, v___x_4032_);
        v___x_4034_ = crate::leanh::lean_unsigned_to_nat(2);
        v_arr_4035_ = l_Lean_Syntax_getArg(v_x_4021_, v___x_4034_);
        v___x_4036_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_4037_ = l_Lean_Syntax_getArg(v_x_4021_, v___x_4036_);
        crate::leanh::lean_dec(v_x_4021_);
        v___x_4038_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__1;
        v___x_4039_ = l_Lean_Syntax_getArgs(v___x_4033_);
        crate::leanh::lean_dec(v___x_4033_);
        v___x_4040_ = 0;
        v___x_4041_ = l_Lean_SourceInfo_fromRef(v_ref_4029_, v___x_4040_);
        v___x_4042_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_4043_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_4041_, 26);
        v___x_4044_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4044_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4044_, 1, v___x_4043_);
        v___x_4045_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4046_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4046_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4046_, 1, v___x_4045_);
        v___x_4047_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4048_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4049_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4050_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0;
        v___x_4051_ = l_Lean_SourceInfo_fromRef(v_tk_4031_, v___x_4026_);
        crate::leanh::lean_dec(v_tk_4031_);
        v___x_4052_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4052_, 0, v___x_4051_);
        crate::leanh::lean_ctor_set(v___x_4052_, 1, v___x_4024_);
        v___x_4053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4054_ = l_Array_append___redArg(v___x_4053_, v___x_4039_);
        crate::leanh::lean_dec_ref(v___x_4039_);
        v___x_4055_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4055_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4055_, 1, v___x_4049_);
        crate::leanh::lean_ctor_set(v___x_4055_, 2, v___x_4054_);
        v___x_4056_ = l_Lean_SourceInfo_fromRef(v_arr_4035_, v___x_4026_);
        crate::leanh::lean_dec(v_arr_4035_);
        v___x_4057_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4057_, 0, v___x_4056_);
        crate::leanh::lean_ctor_set(v___x_4057_, 1, v___x_4045_);
        v___x_4058_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_4059_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_4060_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4060_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4060_, 1, v___x_4059_);
        v___x_4061_ = l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3;
        v___x_4062_ = l_Lean_Parser_Tactic_Conv_paren___closed__1;
        v___x_4063_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        v___x_4064_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4064_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4064_, 1, v___x_4063_);
        v___x_4065_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_4066_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4066_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4066_, 1, v___x_4065_);
        v___x_4067_ = l_Lean_Syntax_node3(
            v___x_4041_,
            v___x_4062_,
            v___x_4064_,
            v___x_4037_,
            v___x_4066_,
        );
        v___x_4068_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2;
        v___x_4069_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4069_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4069_, 1, v___x_4068_);
        v___x_4070_ = l_Lean_Parser_Tactic_Conv_allGoals___closed__1;
        v___x_4071_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1;
        v___x_4072_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4072_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4072_, 1, v___x_4071_);
        v___x_4073_ = l_Lean_Parser_Tactic_Conv_convRfl___closed__1;
        v___x_4074_ = l_Lean_Parser_Tactic_Conv_convRfl___closed__2;
        v___x_4075_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4075_, 0, v___x_4041_);
        crate::leanh::lean_ctor_set(v___x_4075_, 1, v___x_4074_);
        v___x_4076_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4073_, v___x_4075_);
        v___x_4077_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4049_, v___x_4076_);
        v___x_4078_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4061_, v___x_4077_);
        v___x_4079_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4038_, v___x_4078_);
        v___x_4080_ = l_Lean_Syntax_node2(v___x_4041_, v___x_4070_, v___x_4072_, v___x_4079_);
        v___x_4081_ = l_Lean_Syntax_node3(
            v___x_4041_,
            v___x_4049_,
            v___x_4067_,
            v___x_4069_,
            v___x_4080_,
        );
        v___x_4082_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4061_, v___x_4081_);
        v___x_4083_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4038_, v___x_4082_);
        crate::leanh::lean_inc_ref(v___x_4046_);
        v___x_4084_ = l_Lean_Syntax_node3(
            v___x_4041_,
            v___x_4058_,
            v___x_4060_,
            v___x_4046_,
            v___x_4083_,
        );
        v___x_4085_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4049_, v___x_4084_);
        v___x_4086_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4048_, v___x_4085_);
        v___x_4087_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4047_, v___x_4086_);
        v___x_4088_ = l_Lean_Syntax_node4(
            v___x_4041_,
            v___x_4050_,
            v___x_4052_,
            v___x_4055_,
            v___x_4057_,
            v___x_4087_,
        );
        v___x_4089_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4049_, v___x_4088_);
        v___x_4090_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4048_, v___x_4089_);
        v___x_4091_ = l_Lean_Syntax_node1(v___x_4041_, v___x_4047_, v___x_4090_);
        v___x_4092_ = l_Lean_Syntax_node3(
            v___x_4041_,
            v___x_4042_,
            v___x_4044_,
            v___x_4046_,
            v___x_4091_,
        );
        v___x_4093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4093_, 0, v___x_4092_);
        crate::leanh::lean_ctor_set(v___x_4093_, 1, v_a_4023_);
        return v___x_4093_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___boxed(
    mut v_x_4094_: *mut crate::leanh::LeanObject,
    mut v_a_4095_: *mut crate::leanh::LeanObject,
    mut v_a_4096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1(v_x_4094_, v_a_4095_, v_a_4096_);
    crate::leanh::lean_dec_ref(v_a_4095_);
    return v_res_4097_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4109_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__6,
    );
    v___x_4110_ = l_Lean_Parser_Tactic_Conv_case_x27___closed__3;
    v___x_4111_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4112_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4112_, 0, v___x_4111_);
    crate::leanh::lean_ctor_set(v___x_4112_, 1, v___x_4110_);
    crate::leanh::lean_ctor_set(v___x_4112_, 2, v___x_4109_);
    return v___x_4112_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4113_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5;
    v___x_4114_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__4,
    );
    v___x_4115_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4116_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4116_, 0, v___x_4115_);
    crate::leanh::lean_ctor_set(v___x_4116_, 1, v___x_4114_);
    crate::leanh::lean_ctor_set(v___x_4116_, 2, v___x_4113_);
    return v___x_4116_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4117_ = l_Lean_Parser_Tactic_Conv_convSeq;
    v___x_4118_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__5,
    );
    v___x_4119_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4120_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4120_, 0, v___x_4119_);
    crate::leanh::lean_ctor_set(v___x_4120_, 1, v___x_4118_);
    crate::leanh::lean_ctor_set(v___x_4120_, 2, v___x_4117_);
    return v___x_4120_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4121_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__6,
    );
    v___x_4122_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_4123_ = l_Lean_Parser_Tactic_Conv_case_x27___closed__1;
    v___x_4124_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4124_, 0, v___x_4123_);
    crate::leanh::lean_ctor_set(v___x_4124_, 1, v___x_4122_);
    crate::leanh::lean_ctor_set(v___x_4124_, 2, v___x_4121_);
    return v___x_4124_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27() -> *mut crate::leanh::LeanObject {
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4125_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__7,
    );
    return v___x_4125_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1(
    mut v_x_4131_: *mut crate::leanh::LeanObject,
    mut v_a_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: u8 = 0;
    v___x_4134_ = l_Lean_Parser_Tactic_Conv_case_x27___closed__0;
    v___x_4135_ = l_Lean_Parser_Tactic_Conv_case_x27___closed__1;
    crate::leanh::lean_inc(v_x_4131_);
    v___x_4136_ = l_Lean_Syntax_isOfKind(v_x_4131_, v___x_4135_);
    if v___x_4136_ == 0 {
        let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4131_);
        v___x_4137_ = crate::leanh::lean_box(1);
        v___x_4138_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4138_, 0, v___x_4137_);
        crate::leanh::lean_ctor_set(v___x_4138_, 1, v_a_4133_);
        return v___x_4138_;
    } else {
        let mut v_ref_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_arr_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4149_: u8 = 0;
        let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4139_ = crate::leanh::lean_ctor_get(v_a_4132_, 5);
        v___x_4140_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_4141_ = l_Lean_Syntax_getArg(v_x_4131_, v___x_4140_);
        v___x_4142_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4143_ = l_Lean_Syntax_getArg(v_x_4131_, v___x_4142_);
        v___x_4144_ = crate::leanh::lean_unsigned_to_nat(2);
        v_arr_4145_ = l_Lean_Syntax_getArg(v_x_4131_, v___x_4144_);
        v___x_4146_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_4147_ = l_Lean_Syntax_getArg(v_x_4131_, v___x_4146_);
        crate::leanh::lean_dec(v_x_4131_);
        v___x_4148_ = l_Lean_Syntax_getArgs(v___x_4143_);
        crate::leanh::lean_dec(v___x_4143_);
        v___x_4149_ = 0;
        v___x_4150_ = l_Lean_SourceInfo_fromRef(v_ref_4139_, v___x_4149_);
        v___x_4151_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_4152_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_4150_, 12);
        v___x_4153_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4153_, 0, v___x_4150_);
        crate::leanh::lean_ctor_set(v___x_4153_, 1, v___x_4152_);
        v___x_4154_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4155_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4155_, 0, v___x_4150_);
        crate::leanh::lean_ctor_set(v___x_4155_, 1, v___x_4154_);
        v___x_4156_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4157_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4158_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4159_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0;
        v___x_4160_ = l_Lean_SourceInfo_fromRef(v_tk_4141_, v___x_4136_);
        crate::leanh::lean_dec(v_tk_4141_);
        v___x_4161_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4161_, 0, v___x_4160_);
        crate::leanh::lean_ctor_set(v___x_4161_, 1, v___x_4134_);
        v___x_4162_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4163_ = l_Array_append___redArg(v___x_4162_, v___x_4148_);
        crate::leanh::lean_dec_ref(v___x_4148_);
        v___x_4164_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4164_, 0, v___x_4150_);
        crate::leanh::lean_ctor_set(v___x_4164_, 1, v___x_4158_);
        crate::leanh::lean_ctor_set(v___x_4164_, 2, v___x_4163_);
        v___x_4165_ = l_Lean_SourceInfo_fromRef(v_arr_4145_, v___x_4136_);
        crate::leanh::lean_dec(v_arr_4145_);
        v___x_4166_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4166_, 0, v___x_4165_);
        crate::leanh::lean_ctor_set(v___x_4166_, 1, v___x_4154_);
        v___x_4167_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_4168_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_4169_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4169_, 0, v___x_4150_);
        crate::leanh::lean_ctor_set(v___x_4169_, 1, v___x_4168_);
        crate::leanh::lean_inc_ref(v___x_4155_);
        v___x_4170_ = l_Lean_Syntax_node3(
            v___x_4150_,
            v___x_4167_,
            v___x_4169_,
            v___x_4155_,
            v___x_4147_,
        );
        v___x_4171_ = l_Lean_Syntax_node1(v___x_4150_, v___x_4158_, v___x_4170_);
        v___x_4172_ = l_Lean_Syntax_node1(v___x_4150_, v___x_4157_, v___x_4171_);
        v___x_4173_ = l_Lean_Syntax_node1(v___x_4150_, v___x_4156_, v___x_4172_);
        v___x_4174_ = l_Lean_Syntax_node4(
            v___x_4150_,
            v___x_4159_,
            v___x_4161_,
            v___x_4164_,
            v___x_4166_,
            v___x_4173_,
        );
        v___x_4175_ = l_Lean_Syntax_node1(v___x_4150_, v___x_4158_, v___x_4174_);
        v___x_4176_ = l_Lean_Syntax_node1(v___x_4150_, v___x_4157_, v___x_4175_);
        v___x_4177_ = l_Lean_Syntax_node1(v___x_4150_, v___x_4156_, v___x_4176_);
        v___x_4178_ = l_Lean_Syntax_node3(
            v___x_4150_,
            v___x_4151_,
            v___x_4153_,
            v___x_4155_,
            v___x_4177_,
        );
        v___x_4179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4179_, 0, v___x_4178_);
        crate::leanh::lean_ctor_set(v___x_4179_, 1, v_a_4133_);
        return v___x_4179_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___boxed(
    mut v_x_4180_: *mut crate::leanh::LeanObject,
    mut v_a_4181_: *mut crate::leanh::LeanObject,
    mut v_a_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4183_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1(v_x_4180_, v_a_4181_, v_a_4182_);
    crate::leanh::lean_dec_ref(v_a_4181_);
    return v_res_4183_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4195_ = l_Lean_binderIdent;
    v___x_4196_ = l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10;
    v___x_4197_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4198_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4198_, 0, v___x_4197_);
    crate::leanh::lean_ctor_set(v___x_4198_, 1, v___x_4196_);
    crate::leanh::lean_ctor_set(v___x_4198_, 2, v___x_4195_);
    return v___x_4198_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4199_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4,
    );
    v___x_4200_ = l_Lean_Parser_Tactic_Conv_ext___closed__4;
    v___x_4201_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4201_, 0, v___x_4200_);
    crate::leanh::lean_ctor_set(v___x_4201_, 1, v___x_4199_);
    return v___x_4201_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4202_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5,
    );
    v___x_4203_ = l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3;
    v___x_4204_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4205_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4205_, 0, v___x_4204_);
    crate::leanh::lean_ctor_set(v___x_4205_, 1, v___x_4203_);
    crate::leanh::lean_ctor_set(v___x_4205_, 2, v___x_4202_);
    return v___x_4205_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4206_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5;
    v___x_4207_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6,
    );
    v___x_4208_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4209_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4209_, 0, v___x_4208_);
    crate::leanh::lean_ctor_set(v___x_4209_, 1, v___x_4207_);
    crate::leanh::lean_ctor_set(v___x_4209_, 2, v___x_4206_);
    return v___x_4209_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4210_ = l_Lean_Parser_Tactic_Conv_convSeq;
    v___x_4211_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7,
    );
    v___x_4212_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4213_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4213_, 0, v___x_4212_);
    crate::leanh::lean_ctor_set(v___x_4213_, 1, v___x_4211_);
    crate::leanh::lean_ctor_set(v___x_4213_, 2, v___x_4210_);
    return v___x_4213_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4214_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8,
    );
    v___x_4215_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_4216_ = l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1;
    v___x_4217_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4217_, 0, v___x_4216_);
    crate::leanh::lean_ctor_set(v___x_4217_, 1, v___x_4215_);
    crate::leanh::lean_ctor_set(v___x_4217_, 2, v___x_4214_);
    return v___x_4217_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4218_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9,
    );
    return v___x_4218_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1(
    mut v_x_4236_: *mut crate::leanh::LeanObject,
    mut v_a_4237_: *mut crate::leanh::LeanObject,
    mut v_a_4238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: u8 = 0;
    v___x_4239_ = l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1;
    crate::leanh::lean_inc(v_x_4236_);
    v___x_4240_ = l_Lean_Syntax_isOfKind(v_x_4236_, v___x_4239_);
    if v___x_4240_ == 0 {
        let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4236_);
        v___x_4241_ = crate::leanh::lean_box(1);
        v___x_4242_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4242_, 0, v___x_4241_);
        crate::leanh::lean_ctor_set(v___x_4242_, 1, v_a_4238_);
        return v___x_4242_;
    } else {
        let mut v_ref_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_args_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4250_: u8 = 0;
        let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4243_ = crate::leanh::lean_ctor_get(v_a_4237_, 5);
        v___x_4244_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4245_ = l_Lean_Syntax_getArg(v_x_4236_, v___x_4244_);
        v___x_4246_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_4247_ = l_Lean_Syntax_getArg(v_x_4236_, v___x_4246_);
        crate::leanh::lean_dec(v_x_4236_);
        v___x_4248_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1;
        v_args_4249_ = l_Lean_Syntax_getArgs(v___x_4245_);
        crate::leanh::lean_dec(v___x_4245_);
        v___x_4250_ = 0;
        v___x_4251_ = l_Lean_SourceInfo_fromRef(v_ref_4243_, v___x_4250_);
        v___x_4252_ = l_Lean_Parser_Tactic_Conv_case___closed__0;
        v___x_4253_ = l_Lean_Parser_Tactic_Conv_case___closed__1;
        crate::leanh::lean_inc_n(v___x_4251_, 8);
        v___x_4254_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4254_, 0, v___x_4251_);
        crate::leanh::lean_ctor_set(v___x_4254_, 1, v___x_4252_);
        v___x_4255_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4256_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3;
        v___x_4257_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5;
        v___x_4258_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6;
        v___x_4259_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4259_, 0, v___x_4251_);
        crate::leanh::lean_ctor_set(v___x_4259_, 1, v___x_4258_);
        v___x_4260_ = l_Lean_Syntax_node1(v___x_4251_, v___x_4257_, v___x_4259_);
        v___x_4261_ = l_Lean_Syntax_node1(v___x_4251_, v___x_4248_, v___x_4260_);
        v___x_4262_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4263_ = l_Array_append___redArg(v___x_4262_, v_args_4249_);
        crate::leanh::lean_dec_ref(v_args_4249_);
        v___x_4264_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4264_, 0, v___x_4251_);
        crate::leanh::lean_ctor_set(v___x_4264_, 1, v___x_4255_);
        crate::leanh::lean_ctor_set(v___x_4264_, 2, v___x_4263_);
        v___x_4265_ = l_Lean_Syntax_node2(v___x_4251_, v___x_4256_, v___x_4261_, v___x_4264_);
        v___x_4266_ = l_Lean_Syntax_node1(v___x_4251_, v___x_4255_, v___x_4265_);
        v___x_4267_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4268_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4268_, 0, v___x_4251_);
        crate::leanh::lean_ctor_set(v___x_4268_, 1, v___x_4267_);
        v___x_4269_ = l_Lean_Syntax_node4(
            v___x_4251_,
            v___x_4253_,
            v___x_4254_,
            v___x_4266_,
            v___x_4268_,
            v___x_4247_,
        );
        v___x_4270_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4270_, 0, v___x_4269_);
        crate::leanh::lean_ctor_set(v___x_4270_, 1, v_a_4238_);
        return v___x_4270_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___boxed(
    mut v_x_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4274_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1(v_x_4271_, v_a_4272_, v_a_4273_);
    crate::leanh::lean_dec_ref(v_a_4272_);
    return v_res_4274_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1(
    mut v_x_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: u8 = 0;
    v___x_4303_ = l_Lean_Parser_Tactic_Conv_focus___closed__0;
    v___x_4304_ = l_Lean_Parser_Tactic_Conv_focus___closed__1;
    crate::leanh::lean_inc(v_x_4300_);
    v___x_4305_ = l_Lean_Syntax_isOfKind(v_x_4300_, v___x_4304_);
    if v___x_4305_ == 0 {
        let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4300_);
        v___x_4306_ = crate::leanh::lean_box(1);
        v___x_4307_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4307_, 0, v___x_4306_);
        crate::leanh::lean_ctor_set(v___x_4307_, 1, v_a_4302_);
        return v___x_4307_;
    } else {
        let mut v_ref_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4313_: u8 = 0;
        let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4308_ = crate::leanh::lean_ctor_get(v_a_4301_, 5);
        v___x_4309_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_4310_ = l_Lean_Syntax_getArg(v_x_4300_, v___x_4309_);
        v___x_4311_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4312_ = l_Lean_Syntax_getArg(v_x_4300_, v___x_4311_);
        crate::leanh::lean_dec(v_x_4300_);
        v___x_4313_ = 0;
        v___x_4314_ = l_Lean_SourceInfo_fromRef(v_ref_4308_, v___x_4313_);
        v___x_4315_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_4316_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_4314_, 11);
        v___x_4317_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4317_, 0, v___x_4314_);
        crate::leanh::lean_ctor_set(v___x_4317_, 1, v___x_4316_);
        v___x_4318_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4319_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4319_, 0, v___x_4314_);
        crate::leanh::lean_ctor_set(v___x_4319_, 1, v___x_4318_);
        v___x_4320_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4321_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4322_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4323_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0;
        v___x_4324_ = l_Lean_SourceInfo_fromRef(v_tk_4310_, v___x_4305_);
        crate::leanh::lean_dec(v_tk_4310_);
        v___x_4325_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4325_, 0, v___x_4324_);
        crate::leanh::lean_ctor_set(v___x_4325_, 1, v___x_4303_);
        v___x_4326_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_4327_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_4328_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4328_, 0, v___x_4314_);
        crate::leanh::lean_ctor_set(v___x_4328_, 1, v___x_4327_);
        crate::leanh::lean_inc_ref(v___x_4319_);
        v___x_4329_ = l_Lean_Syntax_node3(
            v___x_4314_,
            v___x_4326_,
            v___x_4328_,
            v___x_4319_,
            v___x_4312_,
        );
        v___x_4330_ = l_Lean_Syntax_node1(v___x_4314_, v___x_4322_, v___x_4329_);
        v___x_4331_ = l_Lean_Syntax_node1(v___x_4314_, v___x_4321_, v___x_4330_);
        v___x_4332_ = l_Lean_Syntax_node1(v___x_4314_, v___x_4320_, v___x_4331_);
        v___x_4333_ = l_Lean_Syntax_node2(v___x_4314_, v___x_4323_, v___x_4325_, v___x_4332_);
        v___x_4334_ = l_Lean_Syntax_node1(v___x_4314_, v___x_4322_, v___x_4333_);
        v___x_4335_ = l_Lean_Syntax_node1(v___x_4314_, v___x_4321_, v___x_4334_);
        v___x_4336_ = l_Lean_Syntax_node1(v___x_4314_, v___x_4320_, v___x_4335_);
        v___x_4337_ = l_Lean_Syntax_node3(
            v___x_4314_,
            v___x_4315_,
            v___x_4317_,
            v___x_4319_,
            v___x_4336_,
        );
        v___x_4338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4338_, 0, v___x_4337_);
        crate::leanh::lean_ctor_set(v___x_4338_, 1, v_a_4302_);
        return v___x_4338_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___boxed(
    mut v_x_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4342_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1(v_x_4339_, v_a_4340_, v_a_4341_);
    crate::leanh::lean_dec_ref(v_a_4340_);
    return v_res_4342_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1(
    mut v_x_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: u8 = 0;
    v___x_4391_ = l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1;
    crate::leanh::lean_inc(v_x_4388_);
    v___x_4392_ = l_Lean_Syntax_isOfKind(v_x_4388_, v___x_4391_);
    if v___x_4392_ == 0 {
        let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4388_);
        v___x_4393_ = crate::leanh::lean_box(1);
        v___x_4394_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4394_, 0, v___x_4393_);
        crate::leanh::lean_ctor_set(v___x_4394_, 1, v_a_4390_);
        return v___x_4394_;
    } else {
        let mut v_ref_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4400_: u8 = 0;
        let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4395_ = crate::leanh::lean_ctor_get(v_a_4389_, 5);
        v___x_4396_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4397_ = l_Lean_Syntax_getArg(v_x_4388_, v___x_4396_);
        v___x_4398_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4399_ = l_Lean_Syntax_getArg(v_x_4388_, v___x_4398_);
        crate::leanh::lean_dec(v_x_4388_);
        v___x_4400_ = 0;
        v___x_4401_ = l_Lean_SourceInfo_fromRef(v_ref_4395_, v___x_4400_);
        v___x_4402_ = l_Lean_Parser_Tactic_Conv_nestedConv___closed__1;
        v___x_4403_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1;
        v___x_4404_ = l_Lean_SourceInfo_fromRef(v___x_4397_, v___x_4392_);
        crate::leanh::lean_dec(v___x_4397_);
        v___x_4405_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2;
        v___x_4406_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4406_, 0, v___x_4404_);
        crate::leanh::lean_ctor_set(v___x_4406_, 1, v___x_4405_);
        v___x_4407_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4408_ = l_Lean_Parser_Tactic_Conv_paren___closed__1;
        v___x_4409_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        crate::leanh::lean_inc_n(v___x_4401_, 6);
        v___x_4410_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4410_, 0, v___x_4401_);
        crate::leanh::lean_ctor_set(v___x_4410_, 1, v___x_4409_);
        v___x_4411_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_4412_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4412_, 0, v___x_4401_);
        crate::leanh::lean_ctor_set(v___x_4412_, 1, v___x_4411_);
        v___x_4413_ = l_Lean_Syntax_node3(
            v___x_4401_,
            v___x_4408_,
            v___x_4410_,
            v___x_4399_,
            v___x_4412_,
        );
        v___x_4414_ = l_Lean_Syntax_node1(v___x_4401_, v___x_4407_, v___x_4413_);
        v___x_4415_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11;
        v___x_4416_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4416_, 0, v___x_4401_);
        crate::leanh::lean_ctor_set(v___x_4416_, 1, v___x_4415_);
        v___x_4417_ = l_Lean_Syntax_node3(
            v___x_4401_,
            v___x_4403_,
            v___x_4406_,
            v___x_4414_,
            v___x_4416_,
        );
        v___x_4418_ = l_Lean_Syntax_node1(v___x_4401_, v___x_4402_, v___x_4417_);
        v___x_4419_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4419_, 0, v___x_4418_);
        crate::leanh::lean_ctor_set(v___x_4419_, 1, v_a_4390_);
        return v___x_4419_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1___boxed(
    mut v_x_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4423_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1(v_x_4420_, v_a_4421_, v_a_4422_);
    crate::leanh::lean_dec_ref(v_a_4421_);
    return v_res_4423_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1(
    mut v_x_4450_: *mut crate::leanh::LeanObject,
    mut v_a_4451_: *mut crate::leanh::LeanObject,
    mut v_a_4452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: u8 = 0;
    v___x_4453_ = l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1;
    crate::leanh::lean_inc(v_x_4450_);
    v___x_4454_ = l_Lean_Syntax_isOfKind(v_x_4450_, v___x_4453_);
    if v___x_4454_ == 0 {
        let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4450_);
        v___x_4455_ = crate::leanh::lean_box(1);
        v___x_4456_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4456_, 0, v___x_4455_);
        crate::leanh::lean_ctor_set(v___x_4456_, 1, v_a_4452_);
        return v___x_4456_;
    } else {
        let mut v_ref_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4462_: u8 = 0;
        let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4457_ = crate::leanh::lean_ctor_get(v_a_4451_, 5);
        v___x_4458_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_4459_ = l_Lean_Syntax_getArg(v_x_4450_, v___x_4458_);
        v___x_4460_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4461_ = l_Lean_Syntax_getArg(v_x_4450_, v___x_4460_);
        crate::leanh::lean_dec(v_x_4450_);
        v___x_4462_ = 0;
        v___x_4463_ = l_Lean_SourceInfo_fromRef(v_ref_4457_, v___x_4462_);
        v___x_4464_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_4465_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_4463_, 11);
        v___x_4466_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4466_, 0, v___x_4463_);
        crate::leanh::lean_ctor_set(v___x_4466_, 1, v___x_4465_);
        v___x_4467_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4468_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4468_, 0, v___x_4463_);
        crate::leanh::lean_ctor_set(v___x_4468_, 1, v___x_4467_);
        v___x_4469_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4470_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4471_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4472_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0;
        v___x_4473_ = l_Lean_SourceInfo_fromRef(v_tk_4459_, v___x_4454_);
        crate::leanh::lean_dec(v_tk_4459_);
        v___x_4474_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1;
        v___x_4475_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4475_, 0, v___x_4473_);
        crate::leanh::lean_ctor_set(v___x_4475_, 1, v___x_4474_);
        v___x_4476_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_4477_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_4478_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4478_, 0, v___x_4463_);
        crate::leanh::lean_ctor_set(v___x_4478_, 1, v___x_4477_);
        crate::leanh::lean_inc_ref(v___x_4468_);
        v___x_4479_ = l_Lean_Syntax_node3(
            v___x_4463_,
            v___x_4476_,
            v___x_4478_,
            v___x_4468_,
            v___x_4461_,
        );
        v___x_4480_ = l_Lean_Syntax_node1(v___x_4463_, v___x_4471_, v___x_4479_);
        v___x_4481_ = l_Lean_Syntax_node1(v___x_4463_, v___x_4470_, v___x_4480_);
        v___x_4482_ = l_Lean_Syntax_node1(v___x_4463_, v___x_4469_, v___x_4481_);
        v___x_4483_ = l_Lean_Syntax_node2(v___x_4463_, v___x_4472_, v___x_4475_, v___x_4482_);
        v___x_4484_ = l_Lean_Syntax_node1(v___x_4463_, v___x_4471_, v___x_4483_);
        v___x_4485_ = l_Lean_Syntax_node1(v___x_4463_, v___x_4470_, v___x_4484_);
        v___x_4486_ = l_Lean_Syntax_node1(v___x_4463_, v___x_4469_, v___x_4485_);
        v___x_4487_ = l_Lean_Syntax_node3(
            v___x_4463_,
            v___x_4464_,
            v___x_4466_,
            v___x_4468_,
            v___x_4486_,
        );
        v___x_4488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4488_, 0, v___x_4487_);
        crate::leanh::lean_ctor_set(v___x_4488_, 1, v_a_4452_);
        return v___x_4488_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___boxed(
    mut v_x_4489_: *mut crate::leanh::LeanObject,
    mut v_a_4490_: *mut crate::leanh::LeanObject,
    mut v_a_4491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1(v_x_4489_, v_a_4490_, v_a_4491_);
    crate::leanh::lean_dec_ref(v_a_4490_);
    return v_res_4492_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4504_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4505_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3;
    v___x_4506_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4507_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4507_, 0, v___x_4506_);
    crate::leanh::lean_ctor_set(v___x_4507_, 1, v___x_4505_);
    crate::leanh::lean_ctor_set(v___x_4507_, 2, v___x_4504_);
    return v___x_4507_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4508_ = l_Lean_Parser_Tactic_rwRuleSeq;
    v___x_4509_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4,
    );
    v___x_4510_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4511_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4511_, 0, v___x_4510_);
    crate::leanh::lean_ctor_set(v___x_4511_, 1, v___x_4509_);
    crate::leanh::lean_ctor_set(v___x_4511_, 2, v___x_4508_);
    return v___x_4511_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4512_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5,
    );
    v___x_4513_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_4514_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1;
    v___x_4515_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4515_, 0, v___x_4514_);
    crate::leanh::lean_ctor_set(v___x_4515_, 1, v___x_4513_);
    crate::leanh::lean_ctor_set(v___x_4515_, 2, v___x_4512_);
    return v___x_4515_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convRw____() -> *mut crate::leanh::LeanObject {
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4516_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6,
    );
    return v___x_4516_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1(
    mut v_x_4517_: *mut crate::leanh::LeanObject,
    mut v_a_4518_: *mut crate::leanh::LeanObject,
    mut v_a_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: u8 = 0;
    v___x_4520_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1;
    crate::leanh::lean_inc(v_x_4517_);
    v___x_4521_ = l_Lean_Syntax_isOfKind(v_x_4517_, v___x_4520_);
    if v___x_4521_ == 0 {
        let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4517_);
        v___x_4522_ = crate::leanh::lean_box(1);
        v___x_4523_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4523_, 0, v___x_4522_);
        crate::leanh::lean_ctor_set(v___x_4523_, 1, v_a_4519_);
        return v___x_4523_;
    } else {
        let mut v_ref_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4529_: u8 = 0;
        let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4524_ = crate::leanh::lean_ctor_get(v_a_4518_, 5);
        v___x_4525_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4526_ = l_Lean_Syntax_getArg(v_x_4517_, v___x_4525_);
        v___x_4527_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_4528_ = l_Lean_Syntax_getArg(v_x_4517_, v___x_4527_);
        crate::leanh::lean_dec(v_x_4517_);
        v___x_4529_ = 0;
        v___x_4530_ = l_Lean_SourceInfo_fromRef(v_ref_4524_, v___x_4529_);
        v___x_4531_ = l_Lean_Parser_Tactic_Conv_rewrite___closed__0;
        v___x_4532_ = l_Lean_Parser_Tactic_Conv_rewrite___closed__1;
        crate::leanh::lean_inc(v___x_4530_);
        v___x_4533_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4533_, 0, v___x_4530_);
        crate::leanh::lean_ctor_set(v___x_4533_, 1, v___x_4531_);
        v___x_4534_ = l_Lean_Syntax_node3(
            v___x_4530_,
            v___x_4532_,
            v___x_4533_,
            v___x_4526_,
            v___x_4528_,
        );
        v___x_4535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4535_, 0, v___x_4534_);
        crate::leanh::lean_ctor_set(v___x_4535_, 1, v_a_4519_);
        return v___x_4535_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1___boxed(
    mut v_x_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4539_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1(v_x_4536_, v_a_4537_, v_a_4538_);
    crate::leanh::lean_dec_ref(v_a_4537_);
    return v_res_4539_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4551_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4552_ = l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3;
    v___x_4553_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4554_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4554_, 0, v___x_4553_);
    crate::leanh::lean_ctor_set(v___x_4554_, 1, v___x_4552_);
    crate::leanh::lean_ctor_set(v___x_4554_, 2, v___x_4551_);
    return v___x_4554_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4555_ = l_Lean_Parser_Tactic_rwRuleSeq;
    v___x_4556_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4,
    );
    v___x_4557_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4558_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4558_, 0, v___x_4557_);
    crate::leanh::lean_ctor_set(v___x_4558_, 1, v___x_4556_);
    crate::leanh::lean_ctor_set(v___x_4558_, 2, v___x_4555_);
    return v___x_4558_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4559_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5,
    );
    v___x_4560_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_4561_ = l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1;
    v___x_4562_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4562_, 0, v___x_4561_);
    crate::leanh::lean_ctor_set(v___x_4562_, 1, v___x_4560_);
    crate::leanh::lean_ctor_set(v___x_4562_, 2, v___x_4559_);
    return v___x_4562_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convErw____() -> *mut crate::leanh::LeanObject {
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4563_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6,
    );
    return v___x_4563_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(
    mut v_sz_4564_: usize,
    mut v_i_4565_: usize,
    mut v_bs_4566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4567_: u8 = 0;
    let mut v_v_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: usize = 0;
    let mut v___x_4572_: usize = 0;
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4567_ = lean_usize_dec_lt(v_i_4565_, v_sz_4564_);
                if v___x_4567_ == 0 {
                    return v_bs_4566_;
                } else {
                    v_v_4568_ = lean_array_uget(v_bs_4566_, v_i_4565_);
                    v___x_4569_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4570_ = lean_array_uset(v_bs_4566_, v_i_4565_, v___x_4569_);
                    v___x_4571_ = 1usize;
                    v___x_4572_ = lean_usize_add(v_i_4565_, v___x_4571_);
                    v___x_4573_ = lean_array_uset(v_bs_x27_4570_, v_i_4565_, v_v_4568_);
                    v_i_4565_ = v___x_4572_;
                    v_bs_4566_ = v___x_4573_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0___boxed(
    mut v_sz_4575_: *mut crate::leanh::LeanObject,
    mut v_i_4576_: *mut crate::leanh::LeanObject,
    mut v_bs_4577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4578_: usize = 0;
    let mut v_i_boxed_4579_: usize = 0;
    let mut v_res_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4578_ = crate::leanh::lean_unbox_usize(v_sz_4575_);
    crate::leanh::lean_dec(v_sz_4575_);
    v_i_boxed_4579_ = crate::leanh::lean_unbox_usize(v_i_4576_);
    crate::leanh::lean_dec(v_i_4576_);
    v_res_4580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(v_sz_boxed_4578_, v_i_boxed_4579_, v_bs_4577_);
    return v_res_4580_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4600_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6;
    v___x_4601_ = l_String_toRawSubstring_x27(v___x_4600_);
    return v___x_4601_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4613_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13;
    v___x_4614_ = l_String_toRawSubstring_x27(v___x_4613_);
    return v___x_4614_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1(
    mut v_x_4632_: *mut crate::leanh::LeanObject,
    mut v_a_4633_: *mut crate::leanh::LeanObject,
    mut v_a_4634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    v___x_4635_ = l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1;
    crate::leanh::lean_inc(v_x_4632_);
    v___x_4636_ = l_Lean_Syntax_isOfKind(v_x_4632_, v___x_4635_);
    if v___x_4636_ == 0 {
        let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4632_);
        v___x_4637_ = crate::leanh::lean_box(1);
        v___x_4638_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4638_, 0, v___x_4637_);
        crate::leanh::lean_ctor_set(v___x_4638_, 1, v_a_4634_);
        return v___x_4638_;
    } else {
        let mut v_quotContext_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4647_: u8 = 0;
        let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4655_: usize = 0;
        let mut v___x_4656_: usize = 0;
        let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_4639_ = crate::leanh::lean_ctor_get(v_a_4633_, 1);
        v_currMacroScope_4640_ = crate::leanh::lean_ctor_get(v_a_4633_, 2);
        v_ref_4641_ = crate::leanh::lean_ctor_get(v_a_4633_, 5);
        v___x_4642_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4643_ = l_Lean_Syntax_getArg(v_x_4632_, v___x_4642_);
        v___x_4644_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_4645_ = l_Lean_Syntax_getArg(v_x_4632_, v___x_4644_);
        crate::leanh::lean_dec(v_x_4632_);
        v___x_4646_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1;
        v___x_4647_ = 0;
        v___x_4648_ = l_Lean_SourceInfo_fromRef(v_ref_4641_, v___x_4647_);
        v___x_4649_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1;
        v___x_4650_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2;
        crate::leanh::lean_inc_n(v___x_4648_, 12);
        v___x_4651_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4651_, 0, v___x_4648_);
        crate::leanh::lean_ctor_set(v___x_4651_, 1, v___x_4650_);
        v___x_4652_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4653_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4654_ = l_Lean_Parser_Tactic_getConfigItems(v___x_4643_);
        v_sz_4655_ = lean_array_size(v___x_4654_);
        v___x_4656_ = 0usize;
        v___x_4657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(v_sz_4655_, v___x_4656_, v___x_4654_);
        v___x_4658_ = l_Array_append___redArg(v___x_4653_, v___x_4657_);
        crate::leanh::lean_dec_ref(v___x_4657_);
        v___x_4659_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3;
        v___x_4660_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5;
        v___x_4661_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        v___x_4662_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4662_, 0, v___x_4648_);
        crate::leanh::lean_ctor_set(v___x_4662_, 1, v___x_4661_);
        v___x_4663_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7);
        v___x_4664_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8;
        crate::leanh::lean_inc_n(v_currMacroScope_4640_, 2);
        crate::leanh::lean_inc_n(v_quotContext_4639_, 2);
        v___x_4665_ =
            l_Lean_addMacroScope(v_quotContext_4639_, v___x_4664_, v_currMacroScope_4640_);
        v___x_4666_ = crate::leanh::lean_box(0);
        v___x_4667_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4667_, 0, v___x_4648_);
        crate::leanh::lean_ctor_set(v___x_4667_, 1, v___x_4663_);
        crate::leanh::lean_ctor_set(v___x_4667_, 2, v___x_4665_);
        crate::leanh::lean_ctor_set(v___x_4667_, 3, v___x_4666_);
        v___x_4668_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9;
        v___x_4669_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4669_, 0, v___x_4648_);
        crate::leanh::lean_ctor_set(v___x_4669_, 1, v___x_4668_);
        v___x_4670_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11;
        v___x_4671_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12;
        v___x_4672_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4672_, 0, v___x_4648_);
        crate::leanh::lean_ctor_set(v___x_4672_, 1, v___x_4671_);
        v___x_4673_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14);
        v___x_4674_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15;
        v___x_4675_ =
            l_Lean_addMacroScope(v_quotContext_4639_, v___x_4674_, v_currMacroScope_4640_);
        v___x_4676_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21;
        v___x_4677_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4677_, 0, v___x_4648_);
        crate::leanh::lean_ctor_set(v___x_4677_, 1, v___x_4673_);
        crate::leanh::lean_ctor_set(v___x_4677_, 2, v___x_4675_);
        crate::leanh::lean_ctor_set(v___x_4677_, 3, v___x_4676_);
        v___x_4678_ = l_Lean_Syntax_node2(v___x_4648_, v___x_4670_, v___x_4672_, v___x_4677_);
        v___x_4679_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_4680_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4680_, 0, v___x_4648_);
        crate::leanh::lean_ctor_set(v___x_4680_, 1, v___x_4679_);
        v___x_4681_ = l_Lean_Syntax_node5(
            v___x_4648_,
            v___x_4660_,
            v___x_4662_,
            v___x_4667_,
            v___x_4669_,
            v___x_4678_,
            v___x_4680_,
        );
        v___x_4682_ = l_Lean_Syntax_node1(v___x_4648_, v___x_4659_, v___x_4681_);
        v___x_4683_ = lean_array_push(v___x_4658_, v___x_4682_);
        v___x_4684_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4684_, 0, v___x_4648_);
        crate::leanh::lean_ctor_set(v___x_4684_, 1, v___x_4652_);
        crate::leanh::lean_ctor_set(v___x_4684_, 2, v___x_4683_);
        v___x_4685_ = l_Lean_Syntax_node1(v___x_4648_, v___x_4646_, v___x_4684_);
        v___x_4686_ = l_Lean_Syntax_node3(
            v___x_4648_,
            v___x_4649_,
            v___x_4651_,
            v___x_4685_,
            v___x_4645_,
        );
        v___x_4687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4687_, 0, v___x_4686_);
        crate::leanh::lean_ctor_set(v___x_4687_, 1, v_a_4634_);
        return v___x_4687_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___boxed(
    mut v_x_4688_: *mut crate::leanh::LeanObject,
    mut v_a_4689_: *mut crate::leanh::LeanObject,
    mut v_a_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4691_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1(v_x_4688_, v_a_4689_, v_a_4690_);
    crate::leanh::lean_dec_ref(v_a_4689_);
    return v_res_4691_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1(
    mut v_x_4708_: *mut crate::leanh::LeanObject,
    mut v_a_4709_: *mut crate::leanh::LeanObject,
    mut v_a_4710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: u8 = 0;
    v___x_4711_ = l_Lean_Parser_Tactic_Conv_convArgs___closed__1;
    v___x_4712_ = l_Lean_Syntax_isOfKind(v_x_4708_, v___x_4711_);
    if v___x_4712_ == 0 {
        let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4713_ = crate::leanh::lean_box(1);
        v___x_4714_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4714_, 0, v___x_4713_);
        crate::leanh::lean_ctor_set(v___x_4714_, 1, v_a_4710_);
        return v___x_4714_;
    } else {
        let mut v_ref_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4716_: u8 = 0;
        let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4715_ = crate::leanh::lean_ctor_get(v_a_4709_, 5);
        v___x_4716_ = 0;
        v___x_4717_ = l_Lean_SourceInfo_fromRef(v_ref_4715_, v___x_4716_);
        v___x_4718_ = l_Lean_Parser_Tactic_Conv_congr___closed__0;
        v___x_4719_ = l_Lean_Parser_Tactic_Conv_congr___closed__1;
        crate::leanh::lean_inc(v___x_4717_);
        v___x_4720_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4720_, 0, v___x_4717_);
        crate::leanh::lean_ctor_set(v___x_4720_, 1, v___x_4718_);
        v___x_4721_ = l_Lean_Syntax_node1(v___x_4717_, v___x_4719_, v___x_4720_);
        v___x_4722_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4722_, 0, v___x_4721_);
        crate::leanh::lean_ctor_set(v___x_4722_, 1, v_a_4710_);
        return v___x_4722_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1___boxed(
    mut v_x_4723_: *mut crate::leanh::LeanObject,
    mut v_a_4724_: *mut crate::leanh::LeanObject,
    mut v_a_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4726_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1(v_x_4723_, v_a_4724_, v_a_4725_);
    crate::leanh::lean_dec_ref(v_a_4724_);
    return v_res_4726_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1(
    mut v_x_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: u8 = 0;
    v___x_4746_ = l_Lean_Parser_Tactic_Conv_convLeft___closed__1;
    v___x_4747_ = l_Lean_Syntax_isOfKind(v_x_4743_, v___x_4746_);
    if v___x_4747_ == 0 {
        let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4748_ = crate::leanh::lean_box(1);
        v___x_4749_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4749_, 0, v___x_4748_);
        crate::leanh::lean_ctor_set(v___x_4749_, 1, v_a_4745_);
        return v___x_4749_;
    } else {
        let mut v_ref_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4751_: u8 = 0;
        let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4750_ = crate::leanh::lean_ctor_get(v_a_4744_, 5);
        v___x_4751_ = 0;
        v___x_4752_ = l_Lean_SourceInfo_fromRef(v_ref_4750_, v___x_4751_);
        v___x_4753_ = l_Lean_Parser_Tactic_Conv_lhs___closed__0;
        v___x_4754_ = l_Lean_Parser_Tactic_Conv_lhs___closed__1;
        crate::leanh::lean_inc(v___x_4752_);
        v___x_4755_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4755_, 0, v___x_4752_);
        crate::leanh::lean_ctor_set(v___x_4755_, 1, v___x_4753_);
        v___x_4756_ = l_Lean_Syntax_node1(v___x_4752_, v___x_4754_, v___x_4755_);
        v___x_4757_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4757_, 0, v___x_4756_);
        crate::leanh::lean_ctor_set(v___x_4757_, 1, v_a_4745_);
        return v___x_4757_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1___boxed(
    mut v_x_4758_: *mut crate::leanh::LeanObject,
    mut v_a_4759_: *mut crate::leanh::LeanObject,
    mut v_a_4760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4761_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1(v_x_4758_, v_a_4759_, v_a_4760_);
    crate::leanh::lean_dec_ref(v_a_4759_);
    return v_res_4761_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1(
    mut v_x_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: u8 = 0;
    v___x_4781_ = l_Lean_Parser_Tactic_Conv_convRight___closed__1;
    v___x_4782_ = l_Lean_Syntax_isOfKind(v_x_4778_, v___x_4781_);
    if v___x_4782_ == 0 {
        let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4783_ = crate::leanh::lean_box(1);
        v___x_4784_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4784_, 0, v___x_4783_);
        crate::leanh::lean_ctor_set(v___x_4784_, 1, v_a_4780_);
        return v___x_4784_;
    } else {
        let mut v_ref_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4786_: u8 = 0;
        let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4785_ = crate::leanh::lean_ctor_get(v_a_4779_, 5);
        v___x_4786_ = 0;
        v___x_4787_ = l_Lean_SourceInfo_fromRef(v_ref_4785_, v___x_4786_);
        v___x_4788_ = l_Lean_Parser_Tactic_Conv_rhs___closed__0;
        v___x_4789_ = l_Lean_Parser_Tactic_Conv_rhs___closed__1;
        crate::leanh::lean_inc(v___x_4787_);
        v___x_4790_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4790_, 0, v___x_4787_);
        crate::leanh::lean_ctor_set(v___x_4790_, 1, v___x_4788_);
        v___x_4791_ = l_Lean_Syntax_node1(v___x_4787_, v___x_4789_, v___x_4790_);
        v___x_4792_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4792_, 0, v___x_4791_);
        crate::leanh::lean_ctor_set(v___x_4792_, 1, v_a_4780_);
        return v___x_4792_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1___boxed(
    mut v_x_4793_: *mut crate::leanh::LeanObject,
    mut v_a_4794_: *mut crate::leanh::LeanObject,
    mut v_a_4795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4796_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1(v_x_4793_, v_a_4794_, v_a_4795_);
    crate::leanh::lean_dec_ref(v_a_4794_);
    return v_res_4796_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4808_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__10,
    );
    v___x_4809_ = l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3;
    v___x_4810_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4811_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4811_, 0, v___x_4810_);
    crate::leanh::lean_ctor_set(v___x_4811_, 1, v___x_4809_);
    crate::leanh::lean_ctor_set(v___x_4811_, 2, v___x_4808_);
    return v___x_4811_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4812_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4,
    );
    v___x_4813_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_4814_ = l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1;
    v___x_4815_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4815_, 0, v___x_4814_);
    crate::leanh::lean_ctor_set(v___x_4815_, 1, v___x_4813_);
    crate::leanh::lean_ctor_set(v___x_4815_, 2, v___x_4812_);
    return v___x_4815_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convIntro______() -> *mut crate::leanh::LeanObject {
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5,
    );
    return v___x_4816_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1(
    mut v_x_4817_: *mut crate::leanh::LeanObject,
    mut v_a_4818_: *mut crate::leanh::LeanObject,
    mut v_a_4819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: u8 = 0;
    v___x_4820_ = l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1;
    crate::leanh::lean_inc(v_x_4817_);
    v___x_4821_ = l_Lean_Syntax_isOfKind(v_x_4817_, v___x_4820_);
    if v___x_4821_ == 0 {
        let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4817_);
        v___x_4822_ = crate::leanh::lean_box(1);
        v___x_4823_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4823_, 0, v___x_4822_);
        crate::leanh::lean_ctor_set(v___x_4823_, 1, v_a_4819_);
        return v___x_4823_;
    } else {
        let mut v_ref_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4828_: u8 = 0;
        let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4824_ = crate::leanh::lean_ctor_get(v_a_4818_, 5);
        v___x_4825_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4826_ = l_Lean_Syntax_getArg(v_x_4817_, v___x_4825_);
        crate::leanh::lean_dec(v_x_4817_);
        v_xs_4827_ = l_Lean_Syntax_getArgs(v___x_4826_);
        crate::leanh::lean_dec(v___x_4826_);
        v___x_4828_ = 0;
        v___x_4829_ = l_Lean_SourceInfo_fromRef(v_ref_4824_, v___x_4828_);
        v___x_4830_ = l_Lean_Parser_Tactic_Conv_ext___closed__0;
        v___x_4831_ = l_Lean_Parser_Tactic_Conv_ext___closed__1;
        crate::leanh::lean_inc_n(v___x_4829_, 2);
        v___x_4832_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4832_, 0, v___x_4829_);
        crate::leanh::lean_ctor_set(v___x_4832_, 1, v___x_4830_);
        v___x_4833_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4834_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4835_ = l_Array_append___redArg(v___x_4834_, v_xs_4827_);
        crate::leanh::lean_dec_ref(v_xs_4827_);
        v___x_4836_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4836_, 0, v___x_4829_);
        crate::leanh::lean_ctor_set(v___x_4836_, 1, v___x_4833_);
        crate::leanh::lean_ctor_set(v___x_4836_, 2, v___x_4835_);
        v___x_4837_ = l_Lean_Syntax_node2(v___x_4829_, v___x_4831_, v___x_4832_, v___x_4836_);
        v___x_4838_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4838_, 0, v___x_4837_);
        crate::leanh::lean_ctor_set(v___x_4838_, 1, v_a_4819_);
        return v___x_4838_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1___boxed(
    mut v_x_4839_: *mut crate::leanh::LeanObject,
    mut v_a_4840_: *mut crate::leanh::LeanObject,
    mut v_a_4841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4842_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1(v_x_4839_, v_a_4840_, v_a_4841_);
    crate::leanh::lean_dec_ref(v_a_4840_);
    return v_res_4842_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4877_ = l_Lean_Parser_Tactic_Conv_enterArg___closed__2;
    v___x_4878_ = l_Lean_binderIdent;
    v___x_4879_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__3;
    v___x_4880_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_4879_);
    crate::leanh::lean_ctor_set(v___x_4880_, 1, v___x_4878_);
    crate::leanh::lean_ctor_set(v___x_4880_, 2, v___x_4877_);
    return v___x_4880_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4881_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enterArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enterArg___closed__3_once),
        _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__3,
    );
    v___x_4882_ = l_Lean_Parser_Tactic_Conv_enterArg___closed__1;
    v___x_4883_ = l_Lean_Parser_Tactic_Conv_enterArg___closed__0;
    v___x_4884_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4884_, 0, v___x_4883_);
    crate::leanh::lean_ctor_set(v___x_4884_, 1, v___x_4882_);
    crate::leanh::lean_ctor_set(v___x_4884_, 2, v___x_4881_);
    return v___x_4884_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enterArg() -> *mut crate::leanh::LeanObject {
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4885_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enterArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enterArg___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__4,
    );
    return v___x_4885_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4900_: u8 = 0;
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4900_ = 0;
    v___x_4901_ = l_Lean_Parser_Tactic_Conv_simp___closed__16;
    v___x_4902_ = l_Lean_Parser_Tactic_Conv_simp___closed__14;
    v___x_4903_ = l_Lean_Parser_Tactic_Conv_enterArg;
    v___x_4904_ = crate::leanh::lean_alloc_ctor(11, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4904_, 0, v___x_4903_);
    crate::leanh::lean_ctor_set(v___x_4904_, 1, v___x_4902_);
    crate::leanh::lean_ctor_set(v___x_4904_, 2, v___x_4901_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4904_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_4900_,
    );
    return v___x_4904_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4905_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__4,
    );
    v___x_4906_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5;
    v___x_4907_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4907_, 0, v___x_4906_);
    crate::leanh::lean_ctor_set(v___x_4907_, 1, v___x_4905_);
    return v___x_4907_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4908_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__5,
    );
    v___x_4909_ = l_Lean_Parser_Tactic_Conv_enter___closed__3;
    v___x_4910_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4911_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4911_, 0, v___x_4910_);
    crate::leanh::lean_ctor_set(v___x_4911_, 1, v___x_4909_);
    crate::leanh::lean_ctor_set(v___x_4911_, 2, v___x_4908_);
    return v___x_4911_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4912_ = l_Lean_Parser_Tactic_Conv_simp___closed__21;
    v___x_4913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__6,
    );
    v___x_4914_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4915_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4915_, 0, v___x_4914_);
    crate::leanh::lean_ctor_set(v___x_4915_, 1, v___x_4913_);
    crate::leanh::lean_ctor_set(v___x_4915_, 2, v___x_4912_);
    return v___x_4915_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__7,
    );
    v___x_4917_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4918_ = l_Lean_Parser_Tactic_Conv_enter___closed__1;
    v___x_4919_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4919_, 0, v___x_4918_);
    crate::leanh::lean_ctor_set(v___x_4919_, 1, v___x_4917_);
    crate::leanh::lean_ctor_set(v___x_4919_, 2, v___x_4916_);
    return v___x_4919_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter() -> *mut crate::leanh::LeanObject {
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__8,
    );
    return v___x_4920_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1(
    mut v_x_4947_: *mut crate::leanh::LeanObject,
    mut v_a_4948_: *mut crate::leanh::LeanObject,
    mut v_a_4949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: u8 = 0;
    v___x_4950_ = l_Lean_Parser_Tactic_Conv_convApply___00__closed__1;
    crate::leanh::lean_inc(v_x_4947_);
    v___x_4951_ = l_Lean_Syntax_isOfKind(v_x_4947_, v___x_4950_);
    if v___x_4951_ == 0 {
        let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4947_);
        v___x_4952_ = crate::leanh::lean_box(1);
        v___x_4953_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4953_, 0, v___x_4952_);
        crate::leanh::lean_ctor_set(v___x_4953_, 1, v_a_4949_);
        return v___x_4953_;
    } else {
        let mut v_ref_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4957_: u8 = 0;
        let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_4954_ = crate::leanh::lean_ctor_get(v_a_4948_, 5);
        v___x_4955_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4956_ = l_Lean_Syntax_getArg(v_x_4947_, v___x_4955_);
        crate::leanh::lean_dec(v_x_4947_);
        v___x_4957_ = 0;
        v___x_4958_ = l_Lean_SourceInfo_fromRef(v_ref_4954_, v___x_4957_);
        v___x_4959_ = l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1;
        v___x_4960_ = l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2;
        crate::leanh::lean_inc_n(v___x_4958_, 7);
        v___x_4961_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4961_, 0, v___x_4958_);
        crate::leanh::lean_ctor_set(v___x_4961_, 1, v___x_4960_);
        v___x_4962_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4963_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4963_, 0, v___x_4958_);
        crate::leanh::lean_ctor_set(v___x_4963_, 1, v___x_4962_);
        v___x_4964_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4965_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4966_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4967_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0;
        v___x_4968_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1;
        v___x_4969_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4969_, 0, v___x_4958_);
        crate::leanh::lean_ctor_set(v___x_4969_, 1, v___x_4967_);
        v___x_4970_ = l_Lean_Syntax_node2(v___x_4958_, v___x_4968_, v___x_4969_, v___x_4956_);
        v___x_4971_ = l_Lean_Syntax_node1(v___x_4958_, v___x_4966_, v___x_4970_);
        v___x_4972_ = l_Lean_Syntax_node1(v___x_4958_, v___x_4965_, v___x_4971_);
        v___x_4973_ = l_Lean_Syntax_node1(v___x_4958_, v___x_4964_, v___x_4972_);
        v___x_4974_ = l_Lean_Syntax_node3(
            v___x_4958_,
            v___x_4959_,
            v___x_4961_,
            v___x_4963_,
            v___x_4973_,
        );
        v___x_4975_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4975_, 0, v___x_4974_);
        crate::leanh::lean_ctor_set(v___x_4975_, 1, v_a_4949_);
        return v___x_4975_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___boxed(
    mut v_x_4976_: *mut crate::leanh::LeanObject,
    mut v_a_4977_: *mut crate::leanh::LeanObject,
    mut v_a_4978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4979_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1(v_x_4976_, v_a_4977_, v_a_4978_);
    crate::leanh::lean_dec_ref(v_a_4977_);
    return v_res_4979_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1(
    mut v_x_5066_: *mut crate::leanh::LeanObject,
    mut v_a_5067_: *mut crate::leanh::LeanObject,
    mut v_a_5068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: u8 = 0;
    v___x_5069_ = l_Lean_Parser_Tactic_Conv_convTry___00__closed__1;
    crate::leanh::lean_inc(v_x_5066_);
    v___x_5070_ = l_Lean_Syntax_isOfKind(v_x_5066_, v___x_5069_);
    if v___x_5070_ == 0 {
        let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5066_);
        v___x_5071_ = crate::leanh::lean_box(1);
        v___x_5072_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5072_, 0, v___x_5071_);
        crate::leanh::lean_ctor_set(v___x_5072_, 1, v_a_5068_);
        return v___x_5072_;
    } else {
        let mut v_ref_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5077_: u8 = 0;
        let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_5073_ = crate::leanh::lean_ctor_get(v_a_5067_, 5);
        v___x_5074_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5075_ = l_Lean_Syntax_getArg(v_x_5066_, v___x_5074_);
        crate::leanh::lean_dec(v_x_5066_);
        v___x_5076_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__1;
        v___x_5077_ = 0;
        v___x_5078_ = l_Lean_SourceInfo_fromRef(v_ref_5073_, v___x_5077_);
        v___x_5079_ = l_Lean_Parser_Tactic_Conv_first___closed__0;
        v___x_5080_ = l_Lean_Parser_Tactic_Conv_first___closed__1;
        crate::leanh::lean_inc_n(v___x_5078_, 10);
        v___x_5081_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5081_, 0, v___x_5078_);
        crate::leanh::lean_ctor_set(v___x_5081_, 1, v___x_5079_);
        v___x_5082_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_5083_ = l_Lean_Parser_Tactic_Conv_first___closed__7;
        v___x_5084_ = l_Lean_Parser_Tactic_Conv_case___closed__4;
        v___x_5085_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5085_, 0, v___x_5078_);
        crate::leanh::lean_ctor_set(v___x_5085_, 1, v___x_5084_);
        crate::leanh::lean_inc_ref(v___x_5085_);
        v___x_5086_ = l_Lean_Syntax_node2(v___x_5078_, v___x_5083_, v___x_5085_, v___x_5075_);
        v___x_5087_ = l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3;
        v___x_5088_ = l_Lean_Parser_Tactic_Conv_skip___closed__0;
        v___x_5089_ = l_Lean_Parser_Tactic_Conv_skip___closed__1;
        v___x_5090_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5090_, 0, v___x_5078_);
        crate::leanh::lean_ctor_set(v___x_5090_, 1, v___x_5088_);
        v___x_5091_ = l_Lean_Syntax_node1(v___x_5078_, v___x_5089_, v___x_5090_);
        v___x_5092_ = l_Lean_Syntax_node1(v___x_5078_, v___x_5082_, v___x_5091_);
        v___x_5093_ = l_Lean_Syntax_node1(v___x_5078_, v___x_5087_, v___x_5092_);
        v___x_5094_ = l_Lean_Syntax_node1(v___x_5078_, v___x_5076_, v___x_5093_);
        v___x_5095_ = l_Lean_Syntax_node2(v___x_5078_, v___x_5083_, v___x_5085_, v___x_5094_);
        v___x_5096_ = l_Lean_Syntax_node2(v___x_5078_, v___x_5082_, v___x_5086_, v___x_5095_);
        v___x_5097_ = l_Lean_Syntax_node2(v___x_5078_, v___x_5080_, v___x_5081_, v___x_5096_);
        v___x_5098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5098_, 0, v___x_5097_);
        crate::leanh::lean_ctor_set(v___x_5098_, 1, v_a_5068_);
        return v___x_5098_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1___boxed(
    mut v_x_5099_: *mut crate::leanh::LeanObject,
    mut v_a_5100_: *mut crate::leanh::LeanObject,
    mut v_a_5101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5102_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1(v_x_5099_, v_a_5100_, v_a_5101_);
    crate::leanh::lean_dec_ref(v_a_5100_);
    return v_res_5102_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1(
    mut v_x_5135_: *mut crate::leanh::LeanObject,
    mut v_a_5136_: *mut crate::leanh::LeanObject,
    mut v_a_5137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: u8 = 0;
    v___x_5138_ = l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1;
    crate::leanh::lean_inc(v_x_5135_);
    v___x_5139_ = l_Lean_Syntax_isOfKind(v_x_5135_, v___x_5138_);
    if v___x_5139_ == 0 {
        let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5135_);
        v___x_5140_ = crate::leanh::lean_box(1);
        v___x_5141_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5141_, 0, v___x_5140_);
        crate::leanh::lean_ctor_set(v___x_5141_, 1, v_a_5137_);
        return v___x_5141_;
    } else {
        let mut v_ref_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5149_: u8 = 0;
        let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_5142_ = crate::leanh::lean_ctor_get(v_a_5136_, 5);
        v___x_5143_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5144_ = l_Lean_Syntax_getArg(v_x_5135_, v___x_5143_);
        v___x_5145_ = crate::leanh::lean_unsigned_to_nat(1);
        v_tk_5146_ = l_Lean_Syntax_getArg(v_x_5135_, v___x_5145_);
        v___x_5147_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_5148_ = l_Lean_Syntax_getArg(v_x_5135_, v___x_5147_);
        crate::leanh::lean_dec(v_x_5135_);
        v___x_5149_ = 0;
        v___x_5150_ = l_Lean_SourceInfo_fromRef(v_ref_5142_, v___x_5149_);
        v___x_5151_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_5152_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        crate::leanh::lean_inc_n(v___x_5150_, 25);
        v___x_5153_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5153_, 0, v___x_5150_);
        crate::leanh::lean_ctor_set(v___x_5153_, 1, v___x_5152_);
        v___x_5154_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_5155_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5155_, 0, v___x_5150_);
        crate::leanh::lean_ctor_set(v___x_5155_, 1, v___x_5154_);
        v___x_5156_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_5157_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_5158_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_5159_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1;
        v___x_5160_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2;
        v___x_5161_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        v___x_5162_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5162_, 0, v___x_5150_);
        crate::leanh::lean_ctor_set(v___x_5162_, 1, v___x_5161_);
        v___x_5163_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_5164_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_5165_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5165_, 0, v___x_5150_);
        crate::leanh::lean_ctor_set(v___x_5165_, 1, v___x_5164_);
        v___x_5166_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__1;
        v___x_5167_ = l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3;
        v___x_5168_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5158_, v___x_5144_);
        v___x_5169_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5167_, v___x_5168_);
        v___x_5170_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5166_, v___x_5169_);
        crate::leanh::lean_inc_ref_n(v___x_5155_, 2);
        crate::leanh::lean_inc_ref(v___x_5165_);
        v___x_5171_ = l_Lean_Syntax_node3(
            v___x_5150_,
            v___x_5163_,
            v___x_5165_,
            v___x_5155_,
            v___x_5170_,
        );
        v___x_5172_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5158_, v___x_5171_);
        v___x_5173_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5157_, v___x_5172_);
        v___x_5174_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5156_, v___x_5173_);
        v___x_5175_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_5176_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5176_, 0, v___x_5150_);
        crate::leanh::lean_ctor_set(v___x_5176_, 1, v___x_5175_);
        crate::leanh::lean_inc_ref(v___x_5176_);
        crate::leanh::lean_inc_ref(v___x_5162_);
        v___x_5177_ = l_Lean_Syntax_node3(
            v___x_5150_,
            v___x_5160_,
            v___x_5162_,
            v___x_5174_,
            v___x_5176_,
        );
        v___x_5178_ = l_Lean_SourceInfo_fromRef(v_tk_5146_, v___x_5139_);
        crate::leanh::lean_dec(v_tk_5146_);
        v___x_5179_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3;
        v___x_5180_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5180_, 0, v___x_5178_);
        crate::leanh::lean_ctor_set(v___x_5180_, 1, v___x_5179_);
        v___x_5181_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5158_, v___x_5148_);
        v___x_5182_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5167_, v___x_5181_);
        v___x_5183_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5166_, v___x_5182_);
        v___x_5184_ = l_Lean_Syntax_node3(
            v___x_5150_,
            v___x_5163_,
            v___x_5165_,
            v___x_5155_,
            v___x_5183_,
        );
        v___x_5185_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5158_, v___x_5184_);
        v___x_5186_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5157_, v___x_5185_);
        v___x_5187_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5156_, v___x_5186_);
        v___x_5188_ = l_Lean_Syntax_node3(
            v___x_5150_,
            v___x_5160_,
            v___x_5162_,
            v___x_5187_,
            v___x_5176_,
        );
        v___x_5189_ = l_Lean_Syntax_node3(
            v___x_5150_,
            v___x_5159_,
            v___x_5177_,
            v___x_5180_,
            v___x_5188_,
        );
        v___x_5190_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5158_, v___x_5189_);
        v___x_5191_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5157_, v___x_5190_);
        v___x_5192_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5156_, v___x_5191_);
        v___x_5193_ = l_Lean_Syntax_node3(
            v___x_5150_,
            v___x_5151_,
            v___x_5153_,
            v___x_5155_,
            v___x_5192_,
        );
        v___x_5194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5194_, 0, v___x_5193_);
        crate::leanh::lean_ctor_set(v___x_5194_, 1, v_a_5137_);
        return v___x_5194_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___boxed(
    mut v_x_5195_: *mut crate::leanh::LeanObject,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
    mut v_a_5197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1(v_x_5195_, v_a_5196_, v_a_5197_);
    crate::leanh::lean_dec_ref(v_a_5196_);
    return v_res_5198_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1(
    mut v_x_5220_: *mut crate::leanh::LeanObject,
    mut v_a_5221_: *mut crate::leanh::LeanObject,
    mut v_a_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: u8 = 0;
    v___x_5223_ = l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1;
    crate::leanh::lean_inc(v_x_5220_);
    v___x_5224_ = l_Lean_Syntax_isOfKind(v_x_5220_, v___x_5223_);
    if v___x_5224_ == 0 {
        let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5220_);
        v___x_5225_ = crate::leanh::lean_box(1);
        v___x_5226_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5226_, 0, v___x_5225_);
        crate::leanh::lean_ctor_set(v___x_5226_, 1, v_a_5222_);
        return v___x_5226_;
    } else {
        let mut v_ref_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5231_: u8 = 0;
        let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_5227_ = crate::leanh::lean_ctor_get(v_a_5221_, 5);
        v___x_5228_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5229_ = l_Lean_Syntax_getArg(v_x_5220_, v___x_5228_);
        crate::leanh::lean_dec(v_x_5220_);
        v___x_5230_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__1;
        v___x_5231_ = 0;
        v___x_5232_ = l_Lean_SourceInfo_fromRef(v_ref_5227_, v___x_5231_);
        v___x_5233_ = l_Lean_Parser_Tactic_Conv_first___closed__0;
        v___x_5234_ = l_Lean_Parser_Tactic_Conv_first___closed__1;
        crate::leanh::lean_inc_n(v___x_5232_, 19);
        v___x_5235_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5235_, 0, v___x_5232_);
        crate::leanh::lean_ctor_set(v___x_5235_, 1, v___x_5233_);
        v___x_5236_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_5237_ = l_Lean_Parser_Tactic_Conv_first___closed__7;
        v___x_5238_ = l_Lean_Parser_Tactic_Conv_case___closed__4;
        v___x_5239_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5239_, 0, v___x_5232_);
        crate::leanh::lean_ctor_set(v___x_5239_, 1, v___x_5238_);
        v___x_5240_ = l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3;
        v___x_5241_ = l_Lean_Parser_Tactic_Conv_paren___closed__1;
        v___x_5242_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        v___x_5243_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5243_, 0, v___x_5232_);
        crate::leanh::lean_ctor_set(v___x_5243_, 1, v___x_5242_);
        v___x_5244_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_5245_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5245_, 0, v___x_5232_);
        crate::leanh::lean_ctor_set(v___x_5245_, 1, v___x_5244_);
        crate::leanh::lean_inc(v___x_5229_);
        v___x_5246_ = l_Lean_Syntax_node3(
            v___x_5232_,
            v___x_5241_,
            v___x_5243_,
            v___x_5229_,
            v___x_5245_,
        );
        v___x_5247_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2;
        v___x_5248_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5248_, 0, v___x_5232_);
        crate::leanh::lean_ctor_set(v___x_5248_, 1, v___x_5247_);
        v___x_5249_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0;
        v___x_5250_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5250_, 0, v___x_5232_);
        crate::leanh::lean_ctor_set(v___x_5250_, 1, v___x_5249_);
        v___x_5251_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5223_, v___x_5250_, v___x_5229_);
        v___x_5252_ = l_Lean_Syntax_node3(
            v___x_5232_,
            v___x_5236_,
            v___x_5246_,
            v___x_5248_,
            v___x_5251_,
        );
        v___x_5253_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5240_, v___x_5252_);
        v___x_5254_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5230_, v___x_5253_);
        crate::leanh::lean_inc_ref(v___x_5239_);
        v___x_5255_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5237_, v___x_5239_, v___x_5254_);
        v___x_5256_ = l_Lean_Parser_Tactic_Conv_skip___closed__0;
        v___x_5257_ = l_Lean_Parser_Tactic_Conv_skip___closed__1;
        v___x_5258_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5258_, 0, v___x_5232_);
        crate::leanh::lean_ctor_set(v___x_5258_, 1, v___x_5256_);
        v___x_5259_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5257_, v___x_5258_);
        v___x_5260_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5236_, v___x_5259_);
        v___x_5261_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5240_, v___x_5260_);
        v___x_5262_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5230_, v___x_5261_);
        v___x_5263_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5237_, v___x_5239_, v___x_5262_);
        v___x_5264_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5236_, v___x_5255_, v___x_5263_);
        v___x_5265_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5234_, v___x_5235_, v___x_5264_);
        v___x_5266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5266_, 0, v___x_5265_);
        crate::leanh::lean_ctor_set(v___x_5266_, 1, v_a_5222_);
        return v___x_5266_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___boxed(
    mut v_x_5267_: *mut crate::leanh::LeanObject,
    mut v_a_5268_: *mut crate::leanh::LeanObject,
    mut v_a_5269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5270_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1(v_x_5267_, v_a_5268_, v_a_5269_);
    crate::leanh::lean_dec_ref(v_a_5268_);
    return v_res_5270_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5282_ = l_Lean_Parser_Tactic_optConfig;
    v___x_5283_ = l_Lean_Parser_Tactic_Conv_extractLets___closed__3;
    v___x_5284_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_5285_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5285_, 0, v___x_5284_);
    crate::leanh::lean_ctor_set(v___x_5285_, 1, v___x_5283_);
    crate::leanh::lean_ctor_set(v___x_5285_, 2, v___x_5282_);
    return v___x_5285_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5301_ = l_Lean_Parser_Tactic_Conv_extractLets___closed__9;
    v___x_5302_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__4,
    );
    v___x_5303_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_5304_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5304_, 0, v___x_5303_);
    crate::leanh::lean_ctor_set(v___x_5304_, 1, v___x_5302_);
    crate::leanh::lean_ctor_set(v___x_5304_, 2, v___x_5301_);
    return v___x_5304_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5305_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__10,
    );
    v___x_5306_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_5307_ = l_Lean_Parser_Tactic_Conv_extractLets___closed__1;
    v___x_5308_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5308_, 0, v___x_5307_);
    crate::leanh::lean_ctor_set(v___x_5308_, 1, v___x_5306_);
    crate::leanh::lean_ctor_set(v___x_5308_, 2, v___x_5305_);
    return v___x_5308_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_extractLets() -> *mut crate::leanh::LeanObject {
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5309_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__11_once),
        _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__11,
    );
    return v___x_5309_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5321_ = l_Lean_Parser_Tactic_optConfig;
    v___x_5322_ = l_Lean_Parser_Tactic_Conv_liftLets___closed__3;
    v___x_5323_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_5324_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5324_, 0, v___x_5323_);
    crate::leanh::lean_ctor_set(v___x_5324_, 1, v___x_5322_);
    crate::leanh::lean_ctor_set(v___x_5324_, 2, v___x_5321_);
    return v___x_5324_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5325_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_liftLets___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_liftLets___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__4,
    );
    v___x_5326_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_5327_ = l_Lean_Parser_Tactic_Conv_liftLets___closed__1;
    v___x_5328_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5328_, 0, v___x_5327_);
    crate::leanh::lean_ctor_set(v___x_5328_, 1, v___x_5326_);
    crate::leanh::lean_ctor_set(v___x_5328_, 2, v___x_5325_);
    return v___x_5328_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_liftLets() -> *mut crate::leanh::LeanObject {
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5329_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_liftLets___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_liftLets___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__5,
    );
    return v___x_5329_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Conv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Conv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Category_conv = _init_l_Lean_Parser_Category_conv();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Category_conv);
    l_Lean_Parser_Tactic_Conv_ext = _init_l_Lean_Parser_Tactic_Conv_ext();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_ext);
    l_Lean_Parser_Tactic_Conv_rewrite = _init_l_Lean_Parser_Tactic_Conv_rewrite();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_rewrite);
    l_Lean_Parser_Tactic_Conv_simp = _init_l_Lean_Parser_Tactic_Conv_simp();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_simp);
    l_Lean_Parser_Tactic_Conv_simpTrace = _init_l_Lean_Parser_Tactic_Conv_simpTrace();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_simpTrace);
    l_Lean_Parser_Tactic_Conv_dsimp = _init_l_Lean_Parser_Tactic_Conv_dsimp();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_dsimp);
    l_Lean_Parser_Tactic_Conv_dsimpTrace = _init_l_Lean_Parser_Tactic_Conv_dsimpTrace();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_dsimpTrace);
    l_Lean_Parser_Tactic_Conv_case = _init_l_Lean_Parser_Tactic_Conv_case();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_case);
    l_Lean_Parser_Tactic_Conv_case_x27 = _init_l_Lean_Parser_Tactic_Conv_case_x27();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_case_x27);
    l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__ =
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__);
    l_Lean_Parser_Tactic_Conv_convRw____ = _init_l_Lean_Parser_Tactic_Conv_convRw____();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convRw____);
    l_Lean_Parser_Tactic_Conv_convErw____ = _init_l_Lean_Parser_Tactic_Conv_convErw____();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convErw____);
    l_Lean_Parser_Tactic_Conv_convIntro______ = _init_l_Lean_Parser_Tactic_Conv_convIntro______();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convIntro______);
    l_Lean_Parser_Tactic_Conv_enterArg = _init_l_Lean_Parser_Tactic_Conv_enterArg();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_enterArg);
    l_Lean_Parser_Tactic_Conv_enter = _init_l_Lean_Parser_Tactic_Conv_enter();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_enter);
    l_Lean_Parser_Tactic_Conv_extractLets = _init_l_Lean_Parser_Tactic_Conv_extractLets();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_extractLets);
    l_Lean_Parser_Tactic_Conv_liftLets = _init_l_Lean_Parser_Tactic_Conv_liftLets();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Tactic_Conv_liftLets);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Conv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Conv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Conv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Conv(builtin);
}
