// Lean compiler output
// Module: Lean.DocString.Syntax
// Imports: Lean.Parser.Term.Basic Lean.Parser.Term.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthen, l_Lean_Parser_checkColEq, l_Lean_Parser_checkColGe,
    l_Lean_Parser_checkLinebreakBefore, l_Lean_Parser_orelse, l_Lean_Parser_pushNone,
    l_Lean_Parser_sepBy, l_Lean_Parser_symbol, l_Lean_Parser_withAntiquotSpliceAndSuffix,
    l_Lean_Parser_withPosition,
};
use crate::r#gen::Lean::Parser::Extra::{
    l_Lean_Parser_sepByIndent_formatter___boxed, l_Lean_Parser_sepByIndent_parenthesizer___boxed,
    l_Lean_Parser_symbol_formatter___boxed, l_Lean_Parser_symbol_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Term::Basic::{
    initialize_Lean_Parser_Term_Basic, l_Lean_Parser_Term_structInstField,
    l_Lean_Parser_Term_structInstField_formatter___boxed,
    l_Lean_Parser_Term_structInstField_parenthesizer___boxed, l_Lean_Parser_Term_structInstFields,
    l_Lean_Parser_Term_structInstFields_formatter,
    l_Lean_Parser_Term_structInstFields_parenthesizer, meta_initialize_Lean_Parser_Term_Basic,
    runtime_initialize_Lean_Parser_Term_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
};
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__2_value: LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__3_value: LeanStringObject<5> =
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
        m_data: [113, 117, 111, 116, 0],
    };
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value) as *mut LeanObject,
        5855146430765573009 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [97, 114, 103, 95, 118, 97, 108, 0],
    };
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__5_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_arg__val_quot___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__5_value)
                as *mut LeanObject,
            12510546876269894343 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__6_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value) as *mut LeanObject,
        14065175054779165461 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__7_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__7_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__9_value: LeanStringObject<12> =
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
        m_data: [96, 40, 97, 114, 103, 95, 118, 97, 108, 124, 32, 0],
    };
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__9_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__10_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__10_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__5_value) as *mut LeanObject,
        12510546876269894343 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__11_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__11_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__12_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__13_value: LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__13_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__14_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__15_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__16_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__6_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__17_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__val_quot___closed__18_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__17_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__val_quot___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__18_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_arg__val_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__18_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_arg__val: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_arg__str___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [68, 111, 99, 0],
};
static mut l_Lean_Doc_Syntax_arg__str___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__str___closed__1_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [83, 121, 110, 116, 97, 120, 0],
};
static mut l_Lean_Doc_Syntax_arg__str___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__str___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 114, 103, 95, 115, 116, 114, 0],
};
static mut l_Lean_Doc_Syntax_arg__str___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__2_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_arg__str___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__2_value) as *mut LeanObject,
        16350384043721911836 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__str___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__str___closed__4_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 116, 114, 0],
};
static mut l_Lean_Doc_Syntax_arg__str___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__str___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__4_value) as *mut LeanObject,
        9232979286016572671 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__str___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__str___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__5_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_arg__str___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__str___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__3_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__str___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_arg__str: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__ident___closed__0_value: LeanStringObject<10> =
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
        m_data: [97, 114, 103, 95, 105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Doc_Syntax_arg__ident___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_arg__ident___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__0_value) as *mut LeanObject,
        2451685894574911817 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__ident___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__ident___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_arg__ident___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__ident___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__2_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__ident___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__ident___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__ident___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__ident___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__ident___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_arg__ident: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__num___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 114, 103, 95, 110, 117, 109, 0],
};
static mut l_Lean_Doc_Syntax_arg__num___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_arg__num___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__0_value) as *mut LeanObject,
        14487455678410716942 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__num___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__num___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_arg__num___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__num___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__2_value) as *mut LeanObject,
        6110315075117401315 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__num___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__num___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__3_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_arg__num___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_arg__num___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_arg__num___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_arg__num: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [100, 111, 99, 95, 97, 114, 103, 0],
    };
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value)
                as *mut LeanObject,
            10271305315972196463 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value) as *mut LeanObject,
        7006634365036266973 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value: LeanStringObject<12> =
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
        m_data: [96, 40, 100, 111, 99, 95, 97, 114, 103, 124, 32, 0],
    };
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value) as *mut LeanObject,
        10271305315972196463 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_doc__arg_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_doc__arg_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_doc__arg: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_anon___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [97, 110, 111, 110, 0],
};
static mut l_Lean_Doc_Syntax_anon___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_anon___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_anon___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_anon___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_anon___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__0_value) as *mut LeanObject,
        4061692882929131159 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_anon___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_anon___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_anon___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_anon: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_anon___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [65, 110, 111, 110, 121, 109, 111, 117, 115, 32, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [110, 97, 109, 101, 100, 0],
};
static mut l_Lean_Doc_Syntax_named___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_named___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_named___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_named___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_named___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__0_value) as *mut LeanObject,
        7954595750846190064 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_named___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_named___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_named___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_named___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_named___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__5_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_named___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_named___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_named___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_named___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__9_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_named___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_named: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [78, 97, 109, 101, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named__no__paren___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
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
            110, 97, 109, 101, 100, 95, 110, 111, 95, 112, 97, 114, 101, 110, 0,
        ],
    };
static mut l_Lean_Doc_Syntax_named__no__paren___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
            8539228228387540046 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
            18444330650968222853 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_named__no__paren___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__0_value)
                as *mut LeanObject,
            1862588536603037236 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_named__no__paren___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named__no__paren___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__4_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__6_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_named__no__paren___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named__no__paren___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_named__no__paren___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_named__no__paren___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_named__no__paren___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_named__no__paren: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_named__no__paren___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__on___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [102, 108, 97, 103, 95, 111, 110, 0],
};
static mut l_Lean_Doc_Syntax_flag__on___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_flag__on___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__0_value) as *mut LeanObject,
        3891920175377473180 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_flag__on___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__on___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_flag__on___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__on___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_flag__on___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__on___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_flag__on___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__on___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_flag__on___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_flag__on: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__on___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [66, 111, 111, 108, 101, 97, 110, 32, 102, 108, 97, 103, 44, 32, 116, 117, 114, 110, 101, 100, 32, 111, 110, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__off___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [102, 108, 97, 103, 95, 111, 102, 102, 0],
};
static mut l_Lean_Doc_Syntax_flag__off___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_flag__off___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__0_value) as *mut LeanObject,
        16434802777007652893 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_flag__off___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__off___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_flag__off___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__off___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_flag__off___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__off___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_flag__off___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_flag__off___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_flag__off___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_flag__off: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_flag__off___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [66, 111, 111, 108, 101, 97, 110, 32, 102, 108, 97, 103, 44, 32, 116, 117, 114, 110, 101, 100, 32, 111, 102, 102, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__0_value: LeanStringObject<12> =
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
        m_data: [108, 105, 110, 107, 95, 116, 97, 114, 103, 101, 116, 0],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_link__target_quot___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__0_value)
                as *mut LeanObject,
            6318734869738314825 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_link__target_quot___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value)
                as *mut LeanObject,
            17042141673360298171 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__2_value: LeanStringObject<16> =
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
            96, 40, 108, 105, 110, 107, 95, 116, 97, 114, 103, 101, 116, 124, 32, 0,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__0_value)
                as *mut LeanObject,
            6318734869738314825 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__target_quot___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_link__target_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_link__target_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_link__target: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_url___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 114, 108, 0],
};
static mut l_Lean_Doc_Syntax_url___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_url___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_url___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_url___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_url___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__0_value) as *mut LeanObject,
        14879212058519956833 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_url___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_url___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_named___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_url___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_url___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_url___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_url___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_url___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_url: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_url___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0_value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [65, 32, 85, 82, 76, 32, 116, 97, 114, 103, 101, 116, 44, 32, 119, 114, 105, 116, 116, 101, 110, 32, 101, 120, 112, 108, 105, 99, 105, 116, 108, 121, 46, 32, 85, 115, 101, 32, 115, 113, 117, 97, 114, 101, 32, 98, 114, 97, 99, 107, 101, 116, 115, 32, 102, 111, 114, 32, 97, 32, 110, 97, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 46, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ref___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 101, 102, 0],
};
static mut l_Lean_Doc_Syntax_ref___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_ref___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_ref___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_ref___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_ref___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__0_value) as *mut LeanObject,
        9592559646838605213 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ref___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ref___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [91, 0],
};
static mut l_Lean_Doc_Syntax_ref___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ref___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_ref___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ref___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ref___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ref___closed__5_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_ref___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ref___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__5_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_ref___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ref___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ref___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ref___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ref___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_ref: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0_value: LeanStringObject<86> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [65, 32, 110, 97, 109, 101, 100, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 116, 111, 32, 97, 32, 85, 82, 76, 32, 100, 101, 102, 105, 110, 101, 100, 32, 101, 108, 115, 101, 119, 104, 101, 114, 101, 46, 32, 85, 115, 101, 32, 112, 97, 114, 101, 110, 116, 104, 101, 115, 101, 115, 32, 116, 111, 32, 119, 114, 105, 116, 101, 32, 116, 104, 101, 32, 85, 82, 76, 32, 104, 101, 114, 101, 46, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 110, 108, 105, 110, 101, 0],
    };
static mut l_Lean_Doc_Syntax_inline_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_inline_quot___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__0_value) as *mut LeanObject,
        8159932143332935260 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_inline_quot___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value) as *mut LeanObject,
        9092479130511100962 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__2_value: LeanStringObject<11> =
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
        m_data: [96, 40, 105, 110, 108, 105, 110, 101, 124, 32, 0],
    };
static mut l_Lean_Doc_Syntax_inline_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__0_value) as *mut LeanObject,
        8159932143332935260 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__4_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline_quot___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_inline_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_inline: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_text___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 120, 116, 0],
};
static mut l_Lean_Doc_Syntax_text___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_text___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_text___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_text___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_text___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__0_value) as *mut LeanObject,
        7633771195065472508 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_text___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_text___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_text___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_text: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_text___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [101, 109, 112, 104, 0],
};
static mut l_Lean_Doc_Syntax_emph___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_emph___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_emph___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_emph___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_emph___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__0_value) as *mut LeanObject,
        17275792779021629260 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_emph___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 91, 0],
};
static mut l_Lean_Doc_Syntax_emph___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_emph___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__4_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_emph___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__4_value) as *mut LeanObject,
        2302572775315350313 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_emph___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_emph___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_emph___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_emph___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_emph___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_emph___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_emph: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0_value: LeanStringObject<330> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 330, m_capacity: 330, m_length: 328, m_data: [69, 109, 112, 104, 97, 115, 105, 115, 44, 32, 111, 102, 116, 101, 110, 32, 114, 101, 110, 100, 101, 114, 101, 100, 32, 97, 115, 32, 105, 116, 97, 108, 105, 99, 115, 46, 10, 10, 69, 109, 112, 104, 97, 115, 105, 115, 32, 109, 97, 121, 32, 98, 101, 32, 110, 101, 115, 116, 101, 100, 32, 98, 121, 32, 117, 115, 105, 110, 103, 32, 108, 111, 110, 103, 101, 114, 32, 115, 101, 113, 117, 101, 110, 99, 101, 115, 32, 111, 102, 32, 96, 95, 96, 32, 102, 111, 114, 32, 116, 104, 101, 32, 111, 117, 116, 101, 114, 32, 100, 101, 108, 105, 109, 105, 116, 101, 114, 115, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 10, 82, 101, 109, 101, 109, 98, 101, 114, 58, 32, 95, 95, 97, 108, 119, 97, 121, 115, 32, 98, 117, 116, 116, 101, 114, 32, 116, 104, 101, 32, 95, 114, 117, 103, 98, 114, 195, 184, 100, 95, 32, 98, 101, 102, 111, 114, 101, 32, 97, 100, 100, 105, 110, 103, 32, 116, 111, 112, 112, 105, 110, 103, 115, 33, 95, 95, 10, 96, 96, 96, 10, 72, 101, 114, 101, 44, 32, 116, 104, 101, 32, 111, 117, 116, 101, 114, 32, 96, 95, 95, 96, 32, 105, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 101, 109, 112, 104, 97, 115, 105, 122, 101, 32, 116, 104, 101, 32, 105, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 44, 32, 119, 104, 105, 108, 101, 32, 116, 104, 101, 32, 105, 110, 110, 101, 114, 32, 96, 95, 96, 32, 105, 110, 100, 105, 99, 97, 116, 101, 115, 32, 116, 104, 101, 32, 117, 115, 101, 32, 111, 102, 10, 97, 32, 110, 111, 110, 45, 69, 110, 103, 108, 105, 115, 104, 32, 119, 111, 114, 100, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_bold___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [98, 111, 108, 100, 0],
};
static mut l_Lean_Doc_Syntax_bold___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_bold___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_bold___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_bold___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_bold___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__0_value) as *mut LeanObject,
        826132507934060761 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_bold___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_bold___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [42, 91, 0],
};
static mut l_Lean_Doc_Syntax_bold___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_bold___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_bold___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_bold___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_bold___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_bold___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_bold___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_bold___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_bold___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_bold: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_bold___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0_value: LeanStringObject<166> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 166, m_capacity: 166, m_length: 165, m_data: [66, 111, 108, 100, 32, 101, 109, 112, 104, 97, 115, 105, 115, 46, 10, 10, 65, 32, 115, 105, 110, 103, 108, 101, 32, 96, 42, 96, 32, 115, 117, 102, 102, 105, 99, 101, 115, 32, 116, 111, 32, 109, 97, 107, 101, 32, 116, 101, 120, 116, 32, 98, 111, 108, 100, 46, 32, 85, 115, 105, 110, 103, 32, 96, 95, 96, 32, 102, 111, 114, 32, 101, 109, 112, 104, 97, 115, 105, 115, 46, 10, 10, 66, 111, 108, 100, 32, 116, 101, 120, 116, 32, 109, 97, 121, 32, 98, 101, 32, 110, 101, 115, 116, 101, 100, 32, 98, 121, 32, 117, 115, 105, 110, 103, 32, 108, 111, 110, 103, 101, 114, 32, 115, 101, 113, 117, 101, 110, 99, 101, 115, 32, 111, 102, 32, 96, 42, 96, 32, 102, 111, 114, 32, 116, 104, 101, 32, 111, 117, 116, 101, 114, 32, 100, 101, 108, 105, 109, 105, 116, 101, 114, 115, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [108, 105, 110, 107, 0],
};
static mut l_Lean_Doc_Syntax_link___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_link___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_link___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_link___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_link___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__0_value) as *mut LeanObject,
        5786183721214523521 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [108, 105, 110, 107, 91, 0],
};
static mut l_Lean_Doc_Syntax_link___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_link___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_link: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0_value: LeanStringObject<126> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [65, 32, 108, 105, 110, 107, 46, 32, 84, 104, 101, 32, 108, 105, 110, 107, 39, 115, 32, 116, 97, 114, 103, 101, 116, 32, 109, 97, 121, 32, 101, 105, 116, 104, 101, 114, 32, 98, 101, 32, 97, 32, 99, 111, 110, 99, 114, 101, 116, 101, 32, 85, 82, 76, 32, 40, 119, 114, 105, 116, 116, 101, 110, 32, 105, 110, 32, 112, 97, 114, 101, 110, 116, 104, 101, 115, 101, 115, 41, 32, 111, 114, 32, 97, 32, 110, 97, 109, 101, 100, 32, 85, 82, 76, 10, 40, 119, 114, 105, 116, 116, 101, 110, 32, 105, 110, 32, 115, 113, 117, 97, 114, 101, 32, 98, 114, 97, 99, 107, 101, 116, 115, 41, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_image___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 109, 97, 103, 101, 0],
};
static mut l_Lean_Doc_Syntax_image___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_image___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_image___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_image___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_image___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__0_value) as *mut LeanObject,
        4431944511769375132 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_image___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_image___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [105, 109, 97, 103, 101, 40, 0],
};
static mut l_Lean_Doc_Syntax_image___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_image___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_image___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_image___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_image___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_image___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_image___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_image___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__target_quot___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_image___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_image___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_image___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_image: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_image___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0_value: LeanStringObject<221> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 221, m_capacity: 221, m_length: 220, m_data: [65, 110, 32, 105, 109, 97, 103, 101, 44, 32, 119, 105, 116, 104, 32, 97, 108, 116, 101, 114, 110, 97, 116, 101, 32, 116, 101, 120, 116, 32, 97, 110, 100, 32, 97, 32, 85, 82, 76, 46, 10, 10, 84, 104, 101, 32, 97, 108, 116, 101, 114, 110, 97, 116, 101, 32, 116, 101, 120, 116, 32, 105, 115, 32, 97, 32, 112, 108, 97, 105, 110, 32, 115, 116, 114, 105, 110, 103, 44, 32, 114, 97, 116, 104, 101, 114, 32, 116, 104, 97, 110, 32, 86, 101, 114, 115, 111, 32, 109, 97, 114, 107, 117, 112, 46, 10, 10, 84, 104, 101, 32, 105, 109, 97, 103, 101, 32, 85, 82, 76, 32, 109, 97, 121, 32, 101, 105, 116, 104, 101, 114, 32, 98, 101, 32, 97, 32, 99, 111, 110, 99, 114, 101, 116, 101, 32, 85, 82, 76, 32, 40, 119, 114, 105, 116, 116, 101, 110, 32, 105, 110, 32, 112, 97, 114, 101, 110, 116, 104, 101, 115, 101, 115, 41, 32, 111, 114, 32, 97, 32, 110, 97, 109, 101, 100, 32, 85, 82, 76, 32, 40, 119, 114, 105, 116, 116, 101, 110, 32, 105, 110, 10, 115, 113, 117, 97, 114, 101, 32, 98, 114, 97, 99, 107, 101, 116, 115, 41, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [102, 111, 111, 116, 110, 111, 116, 101, 0],
};
static mut l_Lean_Doc_Syntax_footnote___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_footnote___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_footnote___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_footnote___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_footnote___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__0_value) as *mut LeanObject,
        8931910793042548687 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote___closed__2_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [102, 111, 111, 116, 110, 111, 116, 101, 40, 0],
};
static mut l_Lean_Doc_Syntax_footnote___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_footnote___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_footnote: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0_value: LeanStringObject<93> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [65, 32, 102, 111, 111, 116, 110, 111, 116, 101, 32, 117, 115, 101, 32, 115, 105, 116, 101, 46, 10, 10, 70, 111, 111, 116, 110, 111, 116, 101, 115, 32, 109, 117, 115, 116, 32, 98, 101, 32, 100, 101, 102, 105, 110, 101, 100, 32, 101, 108, 115, 101, 119, 104, 101, 114, 101, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 96, 91, 94, 78, 65, 77, 69, 93, 58, 32, 84, 69, 88, 84, 96, 32, 115, 121, 110, 116, 97, 120, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_linebreak___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 105, 110, 101, 98, 114, 101, 97, 107, 0],
};
static mut l_Lean_Doc_Syntax_linebreak___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_linebreak___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__0_value) as *mut LeanObject,
        14934976377275135948 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_linebreak___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_linebreak___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [108, 105, 110, 101, 33, 0],
};
static mut l_Lean_Doc_Syntax_linebreak___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_linebreak___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_linebreak___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_linebreak___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_linebreak___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_linebreak___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_linebreak___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_linebreak: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_linebreak___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_code___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 111, 100, 101, 0],
};
static mut l_Lean_Doc_Syntax_code___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_code___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_code___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_code___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_code___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__0_value) as *mut LeanObject,
        9119460824152039283 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_code___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_code___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 100, 101, 40, 0],
};
static mut l_Lean_Doc_Syntax_code___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_code___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_code___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_code___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_code___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_code___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_code___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_code___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_code___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_code: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0_value: LeanStringObject<448> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 448, m_capacity: 448, m_length: 447, m_data: [76, 105, 116, 101, 114, 97, 108, 32, 99, 111, 100, 101, 46, 10, 10, 67, 111, 100, 101, 32, 109, 97, 121, 32, 98, 101, 103, 105, 110, 32, 119, 105, 116, 104, 32, 97, 110, 121, 32, 110, 111, 110, 45, 122, 101, 114, 111, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 98, 97, 99, 107, 116, 105, 99, 107, 115, 46, 32, 73, 116, 32, 109, 117, 115, 116, 32, 98, 101, 32, 116, 101, 114, 109, 105, 110, 97, 116, 101, 100, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 110, 117, 109, 98, 101, 114, 44, 10, 97, 110, 100, 32, 105, 116, 32, 109, 97, 121, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 97, 32, 115, 101, 113, 117, 101, 110, 99, 101, 32, 111, 102, 32, 98, 97, 99, 107, 116, 105, 99, 107, 115, 32, 116, 104, 97, 116, 32, 105, 115, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 97, 115, 32, 108, 111, 110, 103, 32, 97, 115, 32, 105, 116, 115, 32, 115, 116, 97, 114, 116, 105, 110, 103, 32, 111, 114, 32, 101, 110, 100, 105, 110, 103, 10, 100, 101, 108, 105, 109, 105, 116, 101, 114, 115, 46, 10, 10, 73, 102, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 97, 110, 100, 32, 108, 97, 115, 116, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 115, 32, 97, 114, 101, 32, 115, 112, 97, 99, 101, 44, 32, 97, 110, 100, 32, 105, 116, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 111, 110, 101, 32, 110, 111, 110, 45, 115, 112, 97, 99, 101, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 44, 32, 116, 104, 101, 110, 10, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 115, 116, 114, 105, 110, 103, 32, 104, 97, 115, 32, 97, 32, 115, 105, 110, 103, 108, 101, 32, 115, 112, 97, 99, 101, 32, 115, 116, 114, 105, 112, 112, 101, 100, 32, 102, 114, 111, 109, 32, 101, 97, 99, 104, 32, 101, 110, 100, 46, 32, 84, 104, 117, 115, 44, 32, 96, 96, 96, 32, 96, 96, 32, 96, 120, 32, 96, 96, 32, 96, 96, 96, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 115, 10, 96, 96, 34, 96, 120, 34, 96, 96, 44, 32, 110, 111, 116, 32, 96, 96, 34, 32, 96, 120, 32, 34, 96, 96, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [114, 111, 108, 101, 0],
};
static mut l_Lean_Doc_Syntax_role___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_role___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_role___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_role___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_role___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__0_value) as *mut LeanObject,
        8038157434449897304 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 111, 108, 101, 123, 0],
};
static mut l_Lean_Doc_Syntax_role___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_role___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__7_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_role___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__7_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_role___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__9_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__10_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__11_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__12_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_role___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_role___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__13_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_role: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0_value: LeanStringObject<762> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 762, m_capacity: 762, m_length: 761, m_data: [65, 32, 95, 114, 111, 108, 101, 95, 58, 32, 97, 110, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 32, 116, 111, 32, 116, 104, 101, 32, 86, 101, 114, 115, 111, 32, 100, 111, 99, 117, 109, 101, 110, 116, 32, 108, 97, 110, 103, 117, 97, 103, 101, 32, 105, 110, 32, 97, 110, 32, 105, 110, 108, 105, 110, 101, 32, 112, 111, 115, 105, 116, 105, 111, 110, 46, 10, 10, 84, 101, 120, 116, 32, 105, 115, 32, 103, 105, 118, 101, 110, 32, 97, 32, 114, 111, 108, 101, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 58, 32, 96, 123, 78, 65, 77, 69, 32, 65, 82, 71, 83, 42, 125, 91, 67, 79, 78, 84, 69, 78, 84, 93, 96, 46, 32, 84, 104, 101, 32, 96, 78, 65, 77, 69, 96, 32, 105, 115, 32, 97, 110, 10, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 116, 104, 97, 116, 32, 100, 101, 116, 101, 114, 109, 105, 110, 101, 115, 32, 119, 104, 105, 99, 104, 32, 114, 111, 108, 101, 32, 105, 115, 32, 98, 101, 105, 110, 103, 32, 117, 115, 101, 100, 44, 32, 97, 107, 105, 110, 32, 116, 111, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 46, 32, 69, 97, 99, 104, 32, 111, 102, 32, 116, 104, 101, 32, 96, 65, 82, 71, 83, 96, 32, 109, 97, 121, 10, 104, 97, 118, 101, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 102, 111, 114, 109, 115, 58, 10, 42, 32, 65, 32, 118, 97, 108, 117, 101, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 44, 32, 110, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 44, 32, 111, 114, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 10, 42, 32, 65, 32, 110, 97, 109, 101, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 44, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 40, 78, 65, 77, 69, 32, 58, 61, 32, 86, 65, 76, 85, 69, 41, 96, 10, 42, 32, 65, 32, 102, 108, 97, 103, 44, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 43, 78, 65, 77, 69, 96, 32, 111, 114, 32, 96, 45, 78, 65, 77, 69, 96, 10, 10, 84, 104, 101, 32, 96, 67, 79, 78, 84, 69, 78, 84, 96, 32, 105, 115, 32, 97, 32, 115, 101, 113, 117, 101, 110, 99, 101, 32, 111, 102, 32, 105, 110, 108, 105, 110, 101, 32, 99, 111, 110, 116, 101, 110, 116, 46, 32, 73, 102, 32, 116, 104, 101, 114, 101, 32, 105, 115, 32, 111, 110, 108, 121, 32, 111, 110, 101, 32, 112, 105, 101, 99, 101, 32, 111, 102, 32, 99, 111, 110, 116, 101, 110, 116, 32, 97, 110, 100, 32, 105, 116, 32, 104, 97, 115, 10, 98, 101, 103, 105, 110, 110, 105, 110, 103, 32, 97, 110, 100, 32, 101, 110, 100, 105, 110, 103, 32, 100, 101, 108, 105, 109, 105, 116, 101, 114, 115, 32, 40, 101, 46, 103, 46, 32, 99, 111, 100, 101, 32, 108, 105, 116, 101, 114, 97, 108, 115, 44, 32, 108, 105, 110, 107, 115, 44, 32, 111, 114, 32, 105, 109, 97, 103, 101, 115, 44, 32, 98, 117, 116, 32, 110, 111, 116, 32, 111, 114, 100, 105, 110, 97, 114, 121, 32, 116, 101, 120, 116, 41, 44, 32, 116, 104, 101, 110, 10, 116, 104, 101, 32, 96, 91, 96, 32, 97, 110, 100, 32, 96, 93, 96, 32, 109, 97, 121, 32, 98, 101, 32, 111, 109, 105, 116, 116, 101, 100, 46, 32, 73, 110, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 44, 32, 96, 96, 32, 123, 78, 65, 77, 69, 32, 65, 82, 71, 83, 42, 125, 96, 120, 96, 32, 96, 96, 32, 105, 115, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 116, 111, 10, 96, 96, 123, 78, 65, 77, 69, 32, 65, 82, 71, 83, 42, 125, 91, 96, 120, 96, 93, 96, 96, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline__math___closed__0_value: LeanStringObject<12> =
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
        m_data: [105, 110, 108, 105, 110, 101, 95, 109, 97, 116, 104, 0],
    };
static mut l_Lean_Doc_Syntax_inline__math___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_inline__math___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__0_value) as *mut LeanObject,
        13146676051664452135 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline__math___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline__math___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [92, 109, 97, 116, 104, 0],
    };
static mut l_Lean_Doc_Syntax_inline__math___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline__math___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline__math___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline__math___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline__math___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_inline__math___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_inline__math___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_inline__math: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_inline__math___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0_value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [73, 110, 108, 105, 110, 101, 32, 109, 97, 116, 104, 101, 109, 97, 116, 105, 99, 97, 108, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 40, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 116, 111, 32, 76, 97, 84, 101, 88, 39, 115, 32, 96, 36, 96, 32, 110, 111, 116, 97, 116, 105, 111, 110, 41, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_display__math___closed__0_value: LeanStringObject<13> =
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
        m_data: [100, 105, 115, 112, 108, 97, 121, 95, 109, 97, 116, 104, 0],
    };
static mut l_Lean_Doc_Syntax_display__math___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_display__math___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_display__math___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
            8539228228387540046 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_display__math___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
            18444330650968222853 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_display__math___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__0_value) as *mut LeanObject,
        17625330591492572857 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_display__math___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_display__math___closed__2_value: LeanStringObject<13> =
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
        m_data: [92, 100, 105, 115, 112, 108, 97, 121, 109, 97, 116, 104, 0],
    };
static mut l_Lean_Doc_Syntax_display__math___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_display__math___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_display__math___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_display__math___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_code___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_display__math___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_display__math___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_display__math___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_display__math: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_display__math___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [68, 105, 115, 112, 108, 97, 121, 45, 109, 111, 100, 101, 32, 109, 97, 116, 104, 101, 109, 97, 116, 105, 99, 97, 108, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [98, 108, 111, 99, 107, 0],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_block_quot___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__0_value) as *mut LeanObject,
        4093857890056796939 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_block_quot___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value) as *mut LeanObject,
        18313248621903840209 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__2_value: LeanStringObject<10> =
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
        m_data: [96, 40, 98, 108, 111, 99, 107, 124, 32, 0],
    };
static mut l_Lean_Doc_Syntax_block_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__0_value) as *mut LeanObject,
        4093857890056796939 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__4_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_block_quot___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_block_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_block_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_block: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_list__item_quot___closed__0_value: LeanStringObject<10> =
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
        m_data: [108, 105, 115, 116, 95, 105, 116, 101, 109, 0],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_list__item_quot___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__0_value)
                as *mut LeanObject,
            15323487558306616519 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_list__item_quot___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value)
                as *mut LeanObject,
            12201068963523095829 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_list__item_quot___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            96, 40, 108, 105, 115, 116, 95, 105, 116, 101, 109, 124, 32, 0,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_list__item_quot___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_list__item_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__0_value)
                as *mut LeanObject,
            15323487558306616519 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_list__item_quot___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_list__item_quot___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_list__item_quot___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_list__item_quot___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_list__item_quot___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_list__item_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_list__item_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_list__item: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_li___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [108, 105, 0],
};
static mut l_Lean_Doc_Syntax_li___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_li___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_li___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_li___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_li___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__0_value) as *mut LeanObject,
        7179854397063619926 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_li___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_li___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_li___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_li___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_li___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_li___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_li___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_li___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_li___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_li___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_li___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_li: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 32, 108, 105, 115, 116, 32, 105, 116, 101, 109, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__0_value: LeanStringObject<10> =
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
        m_data: [100, 101, 115, 99, 95, 105, 116, 101, 109, 0],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_desc__item_quot___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__0_value)
                as *mut LeanObject,
            18415429122335186397 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__3_value)
                as *mut LeanObject,
            4320580253285153079 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            96, 40, 100, 101, 115, 99, 95, 105, 116, 101, 109, 124, 32, 0,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__0_value)
                as *mut LeanObject,
            18415429122335186397 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc__item_quot___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_desc__item_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_desc__item_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_desc__item: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_desc___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 101, 115, 99, 0],
};
static mut l_Lean_Doc_Syntax_desc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_desc___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_desc___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_desc___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_desc___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__0_value) as *mut LeanObject,
        3434039097115290872 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_desc___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l_Lean_Doc_Syntax_desc___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_desc___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_desc___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc___closed__5_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [61, 62, 0],
};
static mut l_Lean_Doc_Syntax_desc___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__5_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_desc___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_desc___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_desc___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_desc___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_desc___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_desc: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_desc___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [65, 32, 100, 101, 115, 99, 114, 105, 112, 116, 105, 111, 110, 32, 111, 102, 32, 97, 110, 32, 105, 116, 101, 109, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [112, 97, 114, 97, 0],
};
static mut l_Lean_Doc_Syntax_para___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_para___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_para___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_para___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_para___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__0_value) as *mut LeanObject,
        10424585805673941106 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_para___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 97, 91, 0],
};
static mut l_Lean_Doc_Syntax_para___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_para___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__4_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_para___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__4_value) as *mut LeanObject,
        17243740965612849207 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_para___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_inline_quot___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_para___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_para___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_para___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_para___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_para___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_para: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [80, 97, 114, 97, 103, 114, 97, 112, 104, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ul___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [117, 108, 0],
};
static mut l_Lean_Doc_Syntax_ul___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_ul___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_ul___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_ul___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_ul___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__0_value) as *mut LeanObject,
        6453691647374023416 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ul___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ul___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 108, 123, 0],
};
static mut l_Lean_Doc_Syntax_ul___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ul___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_ul___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ul___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_list__item_quot___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ul___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ul___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ul___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ul___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ul___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ul___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ul___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_ul: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [85, 110, 111, 114, 100, 101, 114, 101, 100, 32, 76, 105, 115, 116, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_dl___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [100, 108, 0],
};
static mut l_Lean_Doc_Syntax_dl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_dl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_dl___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_dl___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_dl___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__0_value) as *mut LeanObject,
        12155608518000259341 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_dl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_dl___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [100, 108, 123, 0],
};
static mut l_Lean_Doc_Syntax_dl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_dl___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_dl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_dl___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_desc__item_quot___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_dl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_dl___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_dl___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_dl___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_dl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_dl___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_dl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_dl: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_dl___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [68, 101, 115, 99, 114, 105, 112, 116, 105, 111, 110, 32, 108, 105, 115, 116, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [111, 108, 0],
};
static mut l_Lean_Doc_Syntax_ol___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_ol___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_ol___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_ol___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_ol___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__0_value) as *mut LeanObject,
        12480416442879068486 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ol___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [111, 108, 40, 0],
};
static mut l_Lean_Doc_Syntax_ol___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_ol___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ol___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ol___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__6_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_ol___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_ol___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ol___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ul___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ol___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__9_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ol___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__10_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_ol___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_ol___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__11_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_ol: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [79, 114, 100, 101, 114, 101, 100, 32, 108, 105, 115, 116, 32, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [99, 111, 100, 101, 98, 108, 111, 99, 107, 0],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_codeblock___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__0_value) as *mut LeanObject,
        12761800624135336676 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [96, 96, 96, 0],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__4_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_codeblock___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__4_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__ident___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__9_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_codeblock___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__9_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__10_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__9_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__10_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__11_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__12_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__13_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_codeblock___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_codeblock___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__14_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_codeblock: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_codeblock___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0_value: LeanStringObject<1211> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1211, m_capacity: 1211, m_length: 1210, m_data: [65, 32, 99, 111, 100, 101, 32, 98, 108, 111, 99, 107, 32, 116, 104, 97, 116, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 108, 105, 116, 101, 114, 97, 108, 32, 99, 111, 100, 101, 46, 10, 10, 67, 111, 100, 101, 32, 98, 108, 111, 99, 107, 115, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 58, 10, 96, 96, 96, 96, 10, 96, 96, 96, 40, 78, 65, 77, 69, 32, 65, 82, 71, 83, 42, 41, 63, 10, 67, 79, 78, 84, 69, 78, 84, 10, 96, 96, 96, 10, 96, 96, 96, 96, 10, 10, 96, 67, 79, 78, 84, 69, 78, 84, 96, 32, 105, 115, 32, 97, 32, 108, 105, 116, 101, 114, 97, 108, 32, 115, 116, 114, 105, 110, 103, 46, 32, 73, 102, 32, 116, 104, 101, 32, 96, 67, 79, 78, 84, 69, 78, 84, 96, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 97, 32, 115, 101, 113, 117, 101, 110, 99, 101, 32, 111, 102, 32, 116, 104, 114, 101, 101, 32, 111, 114, 32, 109, 111, 114, 101, 32, 98, 97, 99, 107, 116, 105, 99, 107, 115, 44, 32, 116, 104, 101, 110, 10, 116, 104, 101, 32, 111, 112, 101, 110, 105, 110, 103, 32, 97, 110, 100, 32, 99, 108, 111, 115, 105, 110, 103, 32, 96, 32, 96, 96, 96, 32, 96, 32, 40, 99, 97, 108, 108, 101, 100, 32, 95, 102, 101, 110, 99, 101, 115, 95, 41, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 109, 111, 114, 101, 32, 98, 97, 99, 107, 116, 105, 99, 107, 115, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 108, 111, 110, 103, 101, 115, 116, 10, 115, 101, 113, 117, 101, 110, 99, 101, 32, 105, 110, 32, 96, 67, 79, 78, 84, 69, 78, 84, 96, 46, 32, 65, 100, 100, 105, 116, 105, 111, 110, 97, 108, 108, 121, 44, 32, 116, 104, 101, 32, 111, 112, 101, 110, 105, 110, 103, 32, 97, 110, 100, 32, 99, 108, 111, 115, 105, 110, 103, 32, 102, 101, 110, 99, 101, 115, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 10, 98, 97, 99, 107, 116, 105, 99, 107, 115, 46, 10, 10, 73, 102, 32, 96, 78, 65, 77, 69, 96, 32, 97, 110, 100, 32, 96, 65, 82, 71, 83, 96, 32, 97, 114, 101, 32, 110, 111, 116, 32, 112, 114, 111, 118, 105, 100, 101, 100, 44, 32, 116, 104, 101, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 98, 108, 111, 99, 107, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 115, 32, 108, 105, 116, 101, 114, 97, 108, 32, 116, 101, 120, 116, 46, 32, 73, 102, 32, 112, 114, 111, 118, 105, 100, 101, 100, 44, 32, 116, 104, 101, 10, 96, 78, 65, 77, 69, 96, 32, 105, 115, 32, 97, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 116, 104, 97, 116, 32, 115, 101, 108, 101, 99, 116, 115, 32, 97, 110, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 97, 116, 105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 46, 32, 85, 110, 108, 105, 107, 101, 32, 77, 97, 114, 107, 100, 111, 119, 110, 44, 32, 116, 104, 105, 115, 32, 110, 97, 109, 101, 32, 105, 115, 10, 110, 111, 116, 32, 110, 101, 99, 101, 115, 115, 97, 114, 105, 108, 121, 32, 116, 104, 101, 32, 108, 97, 110, 103, 117, 97, 103, 101, 32, 105, 110, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 105, 115, 32, 119, 114, 105, 116, 116, 101, 110, 44, 32, 116, 104, 111, 117, 103, 104, 32, 109, 97, 110, 121, 32, 99, 117, 115, 116, 111, 109, 32, 99, 111, 100, 101, 32, 98, 108, 111, 99, 107, 115, 32, 97, 114, 101, 44, 32, 105, 110, 10, 112, 114, 97, 99, 116, 105, 99, 101, 44, 32, 110, 97, 109, 101, 100, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 108, 97, 110, 103, 117, 97, 103, 101, 32, 116, 104, 97, 116, 32, 116, 104, 101, 121, 32, 99, 111, 110, 116, 97, 105, 110, 46, 32, 96, 78, 65, 77, 69, 96, 32, 105, 115, 32, 109, 111, 114, 101, 32, 97, 107, 105, 110, 32, 116, 111, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 46, 32, 69, 97, 99, 104, 10, 111, 102, 32, 116, 104, 101, 32, 96, 65, 82, 71, 83, 96, 32, 109, 97, 121, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 102, 111, 114, 109, 115, 58, 10, 42, 32, 65, 32, 118, 97, 108, 117, 101, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 44, 32, 110, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 44, 32, 111, 114, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 10, 42, 32, 65, 32, 110, 97, 109, 101, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 44, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 40, 78, 65, 77, 69, 32, 58, 61, 32, 86, 65, 76, 85, 69, 41, 96, 10, 42, 32, 65, 32, 102, 108, 97, 103, 44, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 43, 78, 65, 77, 69, 96, 32, 111, 114, 32, 96, 45, 78, 65, 77, 69, 96, 10, 10, 84, 104, 101, 32, 96, 67, 79, 78, 84, 69, 78, 84, 96, 32, 105, 115, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 101, 100, 32, 97, 99, 99, 111, 114, 100, 105, 110, 103, 32, 116, 111, 32, 116, 104, 101, 32, 105, 110, 100, 101, 110, 116, 97, 116, 105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 102, 101, 110, 99, 101, 115, 46, 32, 73, 102, 32, 116, 104, 101, 32, 102, 101, 110, 99, 101, 115, 32, 97, 114, 101, 32, 105, 110, 100, 101, 110, 116, 101, 100, 10, 96, 110, 96, 32, 115, 112, 97, 99, 101, 115, 44, 32, 116, 104, 101, 110, 32, 96, 110, 96, 32, 115, 112, 97, 99, 101, 115, 32, 97, 114, 101, 32, 114, 101, 109, 111, 118, 101, 100, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 115, 116, 97, 114, 116, 32, 111, 102, 32, 101, 97, 99, 104, 32, 108, 105, 110, 101, 32, 111, 102, 32, 96, 67, 79, 78, 84, 69, 78, 84, 96, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_blockquote___closed__0_value: LeanStringObject<11> =
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
        m_data: [98, 108, 111, 99, 107, 113, 117, 111, 116, 101, 0],
    };
static mut l_Lean_Doc_Syntax_blockquote___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_blockquote___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__0_value) as *mut LeanObject,
        16099003537413514650 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_blockquote___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_blockquote___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [62, 0],
};
static mut l_Lean_Doc_Syntax_blockquote___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_blockquote___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_blockquote___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_blockquote___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_li___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_blockquote___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_blockquote___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_blockquote___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_blockquote: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_blockquote___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0_value: LeanStringObject<92> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [65, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 44, 32, 119, 104, 105, 99, 104, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 97, 32, 115, 101, 113, 117, 101, 110, 99, 101, 32, 111, 102, 32, 98, 108, 111, 99, 107, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 97, 115, 32, 105, 110, 100, 101, 110, 116, 101, 100, 32, 97, 115, 32, 116, 104, 101, 32, 96, 62, 96, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__ref___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [108, 105, 110, 107, 95, 114, 101, 102, 0],
};
static mut l_Lean_Doc_Syntax_link__ref___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_link__ref___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__0_value) as *mut LeanObject,
        11897834843334277669 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link__ref___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__ref___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [93, 58, 0],
};
static mut l_Lean_Doc_Syntax_link__ref___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__ref___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_link__ref___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__ref___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ref___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link__ref___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__ref___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link__ref___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_link__ref___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_link__ref___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_link__ref: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0_value: LeanStringObject<51> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [65, 32, 110, 97, 109, 101, 100, 32, 85, 82, 76, 32, 116, 104, 97, 116, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 105, 110, 32, 108, 105, 110, 107, 115, 32, 97, 110, 100, 32, 105, 109, 97, 103, 101, 115, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote__ref___closed__0_value: LeanStringObject<13> =
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
        m_data: [102, 111, 111, 116, 110, 111, 116, 101, 95, 114, 101, 102, 0],
    };
static mut l_Lean_Doc_Syntax_footnote__ref___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
            8539228228387540046 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
            18444330650968222853 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_footnote__ref___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__0_value) as *mut LeanObject,
        995555897786959865 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote__ref___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote__ref___closed__2_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [91, 94, 0],
    };
static mut l_Lean_Doc_Syntax_footnote__ref___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote__ref___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote__ref___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote__ref___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote__ref___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote__ref___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_link__ref___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote__ref___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote__ref___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote__ref___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_footnote__ref___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_footnote__ref___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_footnote__ref: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_footnote__ref___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 102, 111, 111, 116, 110, 111, 116, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 105, 114, 101, 99, 116, 105, 118, 101, 0],
};
static mut l_Lean_Doc_Syntax_directive___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_directive___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_directive___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_directive___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_directive___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__0_value) as *mut LeanObject,
        13115808082649082939 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [58, 58, 58, 0],
};
static mut l_Lean_Doc_Syntax_directive___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_directive___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__4_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [114, 97, 119, 73, 100, 101, 110, 116, 0],
};
static mut l_Lean_Doc_Syntax_directive___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__4_value) as *mut LeanObject,
        930173994822296688 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__5_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_directive___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__9_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_block_quot___closed__4_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__10_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_emph___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__11_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__12_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__13_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_directive___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_directive___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__14_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_directive: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0_value: LeanStringObject<675> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 675, m_capacity: 675, m_length: 674, m_data: [65, 32, 95, 100, 105, 114, 101, 99, 116, 105, 118, 101, 95, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 97, 110, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 32, 116, 111, 32, 116, 104, 101, 32, 86, 101, 114, 115, 111, 32, 108, 97, 110, 103, 117, 97, 103, 101, 32, 105, 110, 32, 98, 108, 111, 99, 107, 32, 112, 111, 115, 105, 116, 105, 111, 110, 46, 10, 10, 68, 105, 114, 101, 99, 116, 105, 118, 101, 115, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 58, 10, 96, 96, 96, 10, 58, 58, 58, 78, 65, 77, 69, 32, 65, 82, 71, 83, 42, 10, 67, 79, 78, 84, 69, 78, 84, 42, 10, 58, 58, 58, 10, 96, 96, 96, 10, 10, 84, 104, 101, 32, 96, 78, 65, 77, 69, 96, 32, 105, 115, 32, 97, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 116, 104, 97, 116, 32, 100, 101, 116, 101, 114, 109, 105, 110, 101, 115, 32, 119, 104, 105, 99, 104, 32, 100, 105, 114, 101, 99, 116, 105, 118, 101, 32, 105, 115, 32, 98, 101, 105, 110, 103, 32, 117, 115, 101, 100, 44, 32, 97, 107, 105, 110, 32, 116, 111, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 46, 10, 69, 97, 99, 104, 32, 111, 102, 32, 116, 104, 101, 32, 96, 65, 82, 71, 83, 96, 32, 109, 97, 121, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 102, 111, 114, 109, 115, 58, 10, 42, 32, 65, 32, 118, 97, 108, 117, 101, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 44, 32, 110, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 44, 32, 111, 114, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 10, 42, 32, 65, 32, 110, 97, 109, 101, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 44, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 40, 78, 65, 77, 69, 32, 58, 61, 32, 86, 65, 76, 85, 69, 41, 96, 10, 42, 32, 65, 32, 102, 108, 97, 103, 44, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 43, 78, 65, 77, 69, 96, 32, 111, 114, 32, 96, 45, 78, 65, 77, 69, 96, 10, 10, 84, 104, 101, 32, 96, 67, 79, 78, 84, 69, 78, 84, 96, 32, 105, 115, 32, 97, 32, 115, 101, 113, 117, 101, 110, 99, 101, 32, 111, 102, 32, 98, 108, 111, 99, 107, 32, 99, 111, 110, 116, 101, 110, 116, 46, 32, 68, 105, 114, 101, 99, 116, 105, 118, 101, 115, 32, 109, 97, 121, 32, 98, 101, 32, 110, 101, 115, 116, 101, 100, 32, 98, 121, 32, 117, 115, 105, 110, 103, 32, 109, 111, 114, 101, 32, 99, 111, 108, 111, 110, 115, 32, 105, 110, 10, 116, 104, 101, 32, 111, 117, 116, 101, 114, 32, 100, 105, 114, 101, 99, 116, 105, 118, 101, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 10, 58, 58, 58, 58, 111, 117, 116, 101, 114, 32, 43, 102, 108, 97, 103, 32, 40, 97, 114, 103, 32, 58, 61, 32, 53, 41, 10, 65, 32, 112, 97, 114, 97, 103, 114, 97, 112, 104, 46, 10, 58, 58, 58, 105, 110, 110, 101, 114, 32, 34, 108, 97, 98, 101, 108, 34, 10, 42, 32, 49, 10, 42, 32, 50, 10, 58, 58, 58, 10, 58, 58, 58, 58, 10, 96, 96, 96, 10, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_header___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_header___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_header___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_header___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_header___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__0_value) as *mut LeanObject,
        12106318518385607562 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_header___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [104, 101, 97, 100, 101, 114, 40, 0],
};
static mut l_Lean_Doc_Syntax_header___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_header___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__num___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_header___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_header___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_ol___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_header___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_para___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_header___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_header___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_header___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_header___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_header: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_header___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0_value: LeanStringObject<203> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 203, m_capacity: 203, m_length: 202, m_data: [65, 32, 104, 101, 97, 100, 101, 114, 10, 10, 72, 101, 97, 100, 101, 114, 115, 32, 109, 117, 115, 116, 32, 98, 101, 32, 99, 111, 114, 114, 101, 99, 116, 108, 121, 32, 110, 101, 115, 116, 101, 100, 32, 116, 111, 32, 102, 111, 114, 109, 32, 97, 32, 116, 114, 101, 101, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 46, 32, 84, 104, 101, 32, 102, 105, 114, 115, 116, 32, 104, 101, 97, 100, 101, 114, 32, 105, 110, 32, 97, 32, 100, 111, 99, 117, 109, 101, 110, 116, 32, 109, 117, 115, 116, 10, 115, 116, 97, 114, 116, 32, 119, 105, 116, 104, 32, 96, 35, 96, 44, 32, 97, 110, 100, 32, 115, 117, 98, 115, 101, 113, 117, 101, 110, 116, 32, 104, 101, 97, 100, 101, 114, 115, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 97, 116, 32, 109, 111, 115, 116, 32, 111, 110, 101, 32, 109, 111, 114, 101, 32, 96, 35, 96, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 112, 114, 101, 99, 101, 100, 105, 110, 103, 32, 104, 101, 97, 100, 101, 114, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadataContents___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Doc_Syntax_metadataContents___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__0_value) as *mut LeanObject;
static mut l_Lean_Doc_Syntax_metadataContents___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_metadataContents___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [115, 101, 112, 66, 121, 0],
    };
static mut l_Lean_Doc_Syntax_metadataContents___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadataContents___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__2_value)
                as *mut LeanObject,
            10608024464111057092 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadataContents___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__3_value) as *mut LeanObject;
static mut l_Lean_Doc_Syntax_metadataContents___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_metadataContents___closed__6_value: LeanStringObject<11> =
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
        m_data: [105, 114, 114, 101, 108, 101, 118, 97, 110, 116, 0],
    };
static mut l_Lean_Doc_Syntax_metadataContents___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__6_value) as *mut LeanObject;
static mut l_Lean_Doc_Syntax_metadataContents___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_metadataContents___closed__10_value: LeanStringObject<11> =
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
        m_data: [108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 0],
    };
static mut l_Lean_Doc_Syntax_metadataContents___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__10_value) as *mut LeanObject;
static mut l_Lean_Doc_Syntax_metadataContents___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_Syntax_metadataContents___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Doc_Syntax_metadataContents___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Doc_Syntax_metadataContents: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Doc_Syntax_metadata__block___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
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
            109, 101, 116, 97, 100, 97, 116, 97, 95, 98, 108, 111, 99, 107, 0,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
            8539228228387540046 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
            18444330650968222853 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_metadata__block___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__0_value)
                as *mut LeanObject,
            15635760689405348171 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadata__block___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [37, 37, 37, 0],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadata__block___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadata__block___closed__4_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            109, 101, 116, 97, 100, 97, 116, 97, 67, 111, 110, 116, 101, 110, 116, 115, 0,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__4_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
            8539228228387540046 as *mut LeanObject,
        ],
    };
static l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
            18444330650968222853 as *mut LeanObject,
        ],
    };
pub static l_Lean_Doc_Syntax_metadata__block___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__4_value)
                as *mut LeanObject,
            2128351791893423339 as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadata__block___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadata__block___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__7_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadata__block___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__8_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadata__block___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadata__block___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_metadata__block: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadata__block___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [77, 101, 116, 97, 100, 97, 116, 97, 32, 102, 111, 114, 32, 116, 104, 101, 32, 112, 114, 101, 99, 101, 100, 105, 110, 103, 32, 104, 101, 97, 100, 101, 114, 46, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_Term_structInstField_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_Syntax_metadataContents_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadataContents_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadataContents_formatter___closed__2_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_sepByIndent_formatter___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 3,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Doc_Syntax_metadataContents_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_Term_structInstField_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2_value: LeanClosureObject<
    4,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_sepByIndent_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value)
            as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Doc_Syntax_command___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Doc_Syntax_command___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__0_value) as *mut LeanObject;
static l_Lean_Doc_Syntax_command___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_command___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__0_value) as *mut LeanObject,
        8539228228387540046 as *mut LeanObject,
    ],
};
static l_Lean_Doc_Syntax_command___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__str___closed__1_value) as *mut LeanObject,
        18444330650968222853 as *mut LeanObject,
    ],
};
pub static l_Lean_Doc_Syntax_command___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__0_value) as *mut LeanObject,
        5109585754862282403 as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_command___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__1_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_command___closed__2_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 109, 109, 97, 110, 100, 123, 0],
};
static mut l_Lean_Doc_Syntax_command___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__2_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_command___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Doc_Syntax_command___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__3_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_command___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_directive___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_command___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__4_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_command___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_command___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__5_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_command___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_arg__val_quot___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_role___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_command___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__6_value) as *mut LeanObject;
pub static l_Lean_Doc_Syntax_command___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Doc_Syntax_command___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Doc_Syntax_command: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Syntax_command___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0_value: LeanStringObject<391> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 391, m_capacity: 391, m_length: 390, m_data: [65, 32, 98, 108, 111, 99, 107, 45, 108, 101, 118, 101, 108, 32, 99, 111, 109, 109, 97, 110, 100, 44, 32, 119, 104, 105, 99, 104, 32, 105, 110, 118, 111, 107, 101, 115, 32, 97, 110, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 32, 100, 117, 114, 105, 110, 103, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 115, 115, 105, 110, 103, 46, 10, 10, 84, 104, 101, 32, 96, 78, 65, 77, 69, 96, 32, 105, 115, 32, 97, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 116, 104, 97, 116, 32, 100, 101, 116, 101, 114, 109, 105, 110, 101, 115, 32, 119, 104, 105, 99, 104, 32, 99, 111, 109, 109, 97, 110, 100, 32, 105, 115, 32, 98, 101, 105, 110, 103, 32, 117, 115, 101, 100, 44, 32, 97, 107, 105, 110, 32, 116, 111, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 46, 10, 69, 97, 99, 104, 32, 111, 102, 32, 116, 104, 101, 32, 96, 65, 82, 71, 83, 96, 32, 109, 97, 121, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 102, 111, 114, 109, 115, 58, 10, 42, 32, 65, 32, 118, 97, 108, 117, 101, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 44, 32, 110, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 44, 32, 111, 114, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 10, 42, 32, 65, 32, 110, 97, 109, 101, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 44, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 40, 78, 65, 77, 69, 32, 58, 61, 32, 86, 65, 76, 85, 69, 41, 96, 10, 42, 32, 65, 32, 102, 108, 97, 103, 44, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 43, 78, 65, 77, 69, 96, 32, 111, 114, 32, 96, 45, 78, 65, 77, 69, 96, 10, 0]};
static mut l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_Category_arg__val() -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ = lean_box(0);
    return v___x_1420_;
}
pub unsafe fn _init_l_Lean_Parser_Category_doc__arg() -> *mut LeanObject {
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    v___x_1500_ = lean_box(0);
    return v___x_1500_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1()
-> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ = l_Lean_Doc_Syntax_anon___closed__1;
    v___x_1515_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0;
    v___x_1516_ = l_Lean_addBuiltinDocString(v___x_1514_, v___x_1515_);
    return v___x_1516_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___boxed(
    mut v_a_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1518_: *mut LeanObject = core::ptr::null_mut();
    v_res_1518_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1();
    return v_res_1518_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1()
-> *mut LeanObject {
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_Lean_Doc_Syntax_named___closed__1;
    v___x_1555_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0;
    v___x_1556_ = l_Lean_addBuiltinDocString(v___x_1554_, v___x_1555_);
    return v___x_1556_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___boxed(
    mut v_a_1557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1558_: *mut LeanObject = core::ptr::null_mut();
    v_res_1558_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1();
    return v_res_1558_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1()
-> *mut LeanObject {
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    v___x_1579_ = l_Lean_Doc_Syntax_named__no__paren___closed__1;
    v___x_1580_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0;
    v___x_1581_ = l_Lean_addBuiltinDocString(v___x_1579_, v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1___boxed(
    mut v_a_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1583_: *mut LeanObject = core::ptr::null_mut();
    v_res_1583_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1();
    return v_res_1583_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1()
-> *mut LeanObject {
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    v___x_1604_ = l_Lean_Doc_Syntax_flag__on___closed__1;
    v___x_1605_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0;
    v___x_1606_ = l_Lean_addBuiltinDocString(v___x_1604_, v___x_1605_);
    return v___x_1606_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___boxed(
    mut v_a_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1608_: *mut LeanObject = core::ptr::null_mut();
    v_res_1608_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1();
    return v_res_1608_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1()
-> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Lean_Doc_Syntax_flag__off___closed__1;
    v___x_1630_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0;
    v___x_1631_ = l_Lean_addBuiltinDocString(v___x_1629_, v___x_1630_);
    return v___x_1631_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___boxed(
    mut v_a_1632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1633_: *mut LeanObject = core::ptr::null_mut();
    v_res_1633_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1();
    return v_res_1633_;
}
pub unsafe fn _init_l_Lean_Parser_Category_link__target() -> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = lean_box(0);
    return v___x_1663_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1()
-> *mut LeanObject {
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    v___x_1685_ = l_Lean_Doc_Syntax_url___closed__1;
    v___x_1686_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0;
    v___x_1687_ = l_Lean_addBuiltinDocString(v___x_1685_, v___x_1686_);
    return v___x_1687_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___boxed(
    mut v_a_1688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1689_: *mut LeanObject = core::ptr::null_mut();
    v_res_1689_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1();
    return v_res_1689_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1()
-> *mut LeanObject {
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1717_ = l_Lean_Doc_Syntax_ref___closed__1;
    v___x_1718_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0;
    v___x_1719_ = l_Lean_addBuiltinDocString(v___x_1717_, v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___boxed(
    mut v_a_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1721_: *mut LeanObject = core::ptr::null_mut();
    v_res_1721_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1();
    return v_res_1721_;
}
pub unsafe fn _init_l_Lean_Parser_Category_inline() -> *mut LeanObject {
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    v___x_1751_ = lean_box(0);
    return v___x_1751_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1()
-> *mut LeanObject {
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    v___x_1793_ = l_Lean_Doc_Syntax_emph___closed__1;
    v___x_1794_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0;
    v___x_1795_ = l_Lean_addBuiltinDocString(v___x_1793_, v___x_1794_);
    return v___x_1795_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___boxed(
    mut v_a_1796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1797_: *mut LeanObject = core::ptr::null_mut();
    v_res_1797_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1();
    return v_res_1797_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1()
-> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = l_Lean_Doc_Syntax_bold___closed__1;
    v___x_1823_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0;
    v___x_1824_ = l_Lean_addBuiltinDocString(v___x_1822_, v___x_1823_);
    return v___x_1824_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___boxed(
    mut v_a_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1826_: *mut LeanObject = core::ptr::null_mut();
    v_res_1826_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1();
    return v_res_1826_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1()
-> *mut LeanObject {
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    v___x_1855_ = l_Lean_Doc_Syntax_link___closed__1;
    v___x_1856_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0;
    v___x_1857_ = l_Lean_addBuiltinDocString(v___x_1855_, v___x_1856_);
    return v___x_1857_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___boxed(
    mut v_a_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1859_: *mut LeanObject = core::ptr::null_mut();
    v_res_1859_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1();
    return v_res_1859_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1()
-> *mut LeanObject {
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    v___x_1888_ = l_Lean_Doc_Syntax_image___closed__1;
    v___x_1889_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0;
    v___x_1890_ = l_Lean_addBuiltinDocString(v___x_1888_, v___x_1889_);
    return v___x_1890_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___boxed(
    mut v_a_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1892_: *mut LeanObject = core::ptr::null_mut();
    v_res_1892_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1();
    return v_res_1892_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1()
-> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lean_Doc_Syntax_footnote___closed__1;
    v___x_1918_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0;
    v___x_1919_ = l_Lean_addBuiltinDocString(v___x_1917_, v___x_1918_);
    return v___x_1919_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___boxed(
    mut v_a_1920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1921_: *mut LeanObject = core::ptr::null_mut();
    v_res_1921_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1();
    return v_res_1921_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1()
-> *mut LeanObject {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_Doc_Syntax_code___closed__1;
    v___x_1965_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0;
    v___x_1966_ = l_Lean_addBuiltinDocString(v___x_1964_, v___x_1965_);
    return v___x_1966_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___boxed(
    mut v_a_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1968_: *mut LeanObject = core::ptr::null_mut();
    v_res_1968_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1();
    return v_res_1968_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1()
-> *mut LeanObject {
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = l_Lean_Doc_Syntax_role___closed__1;
    v___x_2016_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0;
    v___x_2017_ = l_Lean_addBuiltinDocString(v___x_2015_, v___x_2016_);
    return v___x_2017_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___boxed(
    mut v_a_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2019_: *mut LeanObject = core::ptr::null_mut();
    v_res_2019_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1();
    return v_res_2019_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1()
-> *mut LeanObject {
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    v___x_2040_ = l_Lean_Doc_Syntax_inline__math___closed__1;
    v___x_2041_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0;
    v___x_2042_ = l_Lean_addBuiltinDocString(v___x_2040_, v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___boxed(
    mut v_a_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2044_: *mut LeanObject = core::ptr::null_mut();
    v_res_2044_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1();
    return v_res_2044_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1()
-> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = l_Lean_Doc_Syntax_display__math___closed__1;
    v___x_2066_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0;
    v___x_2067_ = l_Lean_addBuiltinDocString(v___x_2065_, v___x_2066_);
    return v___x_2067_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___boxed(
    mut v_a_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2069_: *mut LeanObject = core::ptr::null_mut();
    v_res_2069_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1();
    return v_res_2069_;
}
pub unsafe fn _init_l_Lean_Parser_Category_block() -> *mut LeanObject {
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    v___x_2099_ = lean_box(0);
    return v___x_2099_;
}
pub unsafe fn _init_l_Lean_Parser_Category_list__item() -> *mut LeanObject {
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    v___x_2129_ = lean_box(0);
    return v___x_2129_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1()
-> *mut LeanObject {
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Lean_Doc_Syntax_li___closed__1;
    v___x_2154_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0;
    v___x_2155_ = l_Lean_addBuiltinDocString(v___x_2153_, v___x_2154_);
    return v___x_2155_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___boxed(
    mut v_a_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2157_: *mut LeanObject = core::ptr::null_mut();
    v_res_2157_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1();
    return v_res_2157_;
}
pub unsafe fn _init_l_Lean_Parser_Category_desc__item() -> *mut LeanObject {
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    v___x_2187_ = lean_box(0);
    return v___x_2187_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1()
-> *mut LeanObject {
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    v___x_2219_ = l_Lean_Doc_Syntax_desc___closed__1;
    v___x_2220_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0;
    v___x_2221_ = l_Lean_addBuiltinDocString(v___x_2219_, v___x_2220_);
    return v___x_2221_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___boxed(
    mut v_a_2222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2223_: *mut LeanObject = core::ptr::null_mut();
    v_res_2223_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1();
    return v_res_2223_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1()
-> *mut LeanObject {
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Lean_Doc_Syntax_para___closed__1;
    v___x_2255_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0;
    v___x_2256_ = l_Lean_addBuiltinDocString(v___x_2254_, v___x_2255_);
    return v___x_2256_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___boxed(
    mut v_a_2257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2258_: *mut LeanObject = core::ptr::null_mut();
    v_res_2258_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1();
    return v_res_2258_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1()
-> *mut LeanObject {
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    v___x_2286_ = l_Lean_Doc_Syntax_ul___closed__1;
    v___x_2287_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0;
    v___x_2288_ = l_Lean_addBuiltinDocString(v___x_2286_, v___x_2287_);
    return v___x_2288_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___boxed(
    mut v_a_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2290_: *mut LeanObject = core::ptr::null_mut();
    v_res_2290_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1();
    return v_res_2290_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1()
-> *mut LeanObject {
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    v___x_2318_ = l_Lean_Doc_Syntax_dl___closed__1;
    v___x_2319_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0;
    v___x_2320_ = l_Lean_addBuiltinDocString(v___x_2318_, v___x_2319_);
    return v___x_2320_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___boxed(
    mut v_a_2321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2322_: *mut LeanObject = core::ptr::null_mut();
    v_res_2322_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1();
    return v_res_2322_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1()
-> *mut LeanObject {
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2362_ = l_Lean_Doc_Syntax_ol___closed__1;
    v___x_2363_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0;
    v___x_2364_ = l_Lean_addBuiltinDocString(v___x_2362_, v___x_2363_);
    return v___x_2364_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___boxed(
    mut v_a_2365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2366_: *mut LeanObject = core::ptr::null_mut();
    v_res_2366_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1();
    return v_res_2366_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1()
-> *mut LeanObject {
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_Lean_Doc_Syntax_codeblock___closed__1;
    v___x_2413_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0;
    v___x_2414_ = l_Lean_addBuiltinDocString(v___x_2412_, v___x_2413_);
    return v___x_2414_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___boxed(
    mut v_a_2415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2416_: *mut LeanObject = core::ptr::null_mut();
    v_res_2416_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1();
    return v_res_2416_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1()
-> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Lean_Doc_Syntax_blockquote___closed__1;
    v___x_2438_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0;
    v___x_2439_ = l_Lean_addBuiltinDocString(v___x_2437_, v___x_2438_);
    return v___x_2439_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___boxed(
    mut v_a_2440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2441_: *mut LeanObject = core::ptr::null_mut();
    v_res_2441_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1();
    return v_res_2441_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1()
-> *mut LeanObject {
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    v___x_2466_ = l_Lean_Doc_Syntax_link__ref___closed__1;
    v___x_2467_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0;
    v___x_2468_ = l_Lean_addBuiltinDocString(v___x_2466_, v___x_2467_);
    return v___x_2468_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___boxed(
    mut v_a_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2470_: *mut LeanObject = core::ptr::null_mut();
    v_res_2470_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1();
    return v_res_2470_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1()
-> *mut LeanObject {
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    v___x_2499_ = l_Lean_Doc_Syntax_footnote__ref___closed__1;
    v___x_2500_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0;
    v___x_2501_ = l_Lean_addBuiltinDocString(v___x_2499_, v___x_2500_);
    return v___x_2501_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___boxed(
    mut v_a_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2503_: *mut LeanObject = core::ptr::null_mut();
    v_res_2503_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1();
    return v_res_2503_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1()
-> *mut LeanObject {
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    v___x_2551_ = l_Lean_Doc_Syntax_directive___closed__1;
    v___x_2552_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0;
    v___x_2553_ = l_Lean_addBuiltinDocString(v___x_2551_, v___x_2552_);
    return v___x_2553_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___boxed(
    mut v_a_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2555_: *mut LeanObject = core::ptr::null_mut();
    v_res_2555_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1();
    return v_res_2555_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1()
-> *mut LeanObject {
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v___x_2592_ = l_Lean_Doc_Syntax_header___closed__1;
    v___x_2593_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0;
    v___x_2594_ = l_Lean_addBuiltinDocString(v___x_2592_, v___x_2593_);
    return v___x_2594_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___boxed(
    mut v_a_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2596_: *mut LeanObject = core::ptr::null_mut();
    v_res_2596_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1();
    return v_res_2596_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__1() -> *mut LeanObject {
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    v___x_2598_ = l_Lean_Doc_Syntax_metadataContents___closed__0;
    v___x_2599_ = l_Lean_Parser_symbol(v___x_2598_);
    return v___x_2599_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__4() -> *mut LeanObject {
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    v___x_2603_ = l_Lean_Doc_Syntax_li___closed__2;
    v___x_2604_ = l_Lean_Parser_symbol(v___x_2603_);
    return v___x_2604_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__5() -> *mut LeanObject {
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2608_: *mut LeanObject = core::ptr::null_mut();
    v___x_2605_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__4_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__4,
    );
    v___x_2606_ = l_Lean_Parser_Term_structInstField;
    v___x_2607_ = l_Lean_Doc_Syntax_metadataContents___closed__3;
    v_p_2608_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_2607_, v___x_2606_, v___x_2605_);
    return v_p_2608_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__7() -> *mut LeanObject {
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    v___x_2610_ = l_Lean_Doc_Syntax_metadataContents___closed__6;
    v___x_2611_ = l_Lean_Parser_checkColGe(v___x_2610_);
    return v___x_2611_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__8() -> *mut LeanObject {
    let mut v_p_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    v_p_2612_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__5_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__5,
    );
    v___x_2613_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__7_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__7,
    );
    v___x_2614_ = l_Lean_Parser_andthen(v___x_2613_, v_p_2612_);
    return v___x_2614_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__9() -> *mut LeanObject {
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    v___x_2615_ = l_Lean_Doc_Syntax_metadataContents___closed__6;
    v___x_2616_ = l_Lean_Parser_checkColEq(v___x_2615_);
    return v___x_2616_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__11() -> *mut LeanObject {
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    v___x_2618_ = l_Lean_Doc_Syntax_metadataContents___closed__10;
    v___x_2619_ = l_Lean_Parser_checkLinebreakBefore(v___x_2618_);
    return v___x_2619_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__12() -> *mut LeanObject {
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    v___x_2620_ = l_Lean_Parser_pushNone;
    v___x_2621_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__11_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__11,
    );
    v___x_2622_ = l_Lean_Parser_andthen(v___x_2621_, v___x_2620_);
    return v___x_2622_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__13() -> *mut LeanObject {
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    v___x_2623_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__12_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__12,
    );
    v___x_2624_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__9_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__9,
    );
    v___x_2625_ = l_Lean_Parser_andthen(v___x_2624_, v___x_2623_);
    return v___x_2625_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__14() -> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    v___x_2626_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__13_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__13,
    );
    v___x_2627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__1_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__1,
    );
    v___x_2628_ = l_Lean_Parser_orelse(v___x_2627_, v___x_2626_);
    return v___x_2628_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__15() -> *mut LeanObject {
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    v___x_2629_ = 1;
    v___x_2630_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__14_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__14,
    );
    v___x_2631_ = l_Lean_Doc_Syntax_metadataContents___closed__0;
    v___x_2632_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__8_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__8,
    );
    v___x_2633_ = l_Lean_Parser_sepBy(v___x_2632_, v___x_2631_, v___x_2630_, v___x_2629_);
    return v___x_2633_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__16() -> *mut LeanObject {
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    v___x_2634_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__15_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__15,
    );
    v___x_2635_ = l_Lean_Parser_withPosition(v___x_2634_);
    return v___x_2635_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents___closed__17() -> *mut LeanObject {
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    v___x_2636_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__16_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__16,
    );
    v___x_2637_ = l_Lean_Parser_Term_structInstFields(v___x_2636_);
    return v___x_2637_;
}
pub unsafe fn _init_l_Lean_Doc_Syntax_metadataContents() -> *mut LeanObject {
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    v___x_2638_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Doc_Syntax_metadataContents___closed__17_once),
        _init_l_Lean_Doc_Syntax_metadataContents___closed__17,
    );
    return v___x_2638_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1()
-> *mut LeanObject {
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    v___x_2671_ = l_Lean_Doc_Syntax_metadata__block___closed__1;
    v___x_2672_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0;
    v___x_2673_ = l_Lean_addBuiltinDocString(v___x_2671_, v___x_2672_);
    return v___x_2673_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___boxed(
    mut v_a_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2675_: *mut LeanObject = core::ptr::null_mut();
    v_res_2675_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1();
    return v_res_2675_;
}
pub unsafe fn l_Lean_Doc_Syntax_metadataContents_formatter(
    mut v_a_2683_: *mut LeanObject,
    mut v_a_2684_: *mut LeanObject,
    mut v_a_2685_: *mut LeanObject,
    mut v_a_2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    v___x_2688_ = l_Lean_Doc_Syntax_metadataContents_formatter___closed__2;
    v___x_2689_ = l_Lean_Parser_Term_structInstFields_formatter(
        v___x_2688_,
        v_a_2683_,
        v_a_2684_,
        v_a_2685_,
        v_a_2686_,
    );
    return v___x_2689_;
}
pub unsafe fn l_Lean_Doc_Syntax_metadataContents_formatter___boxed(
    mut v_a_2690_: *mut LeanObject,
    mut v_a_2691_: *mut LeanObject,
    mut v_a_2692_: *mut LeanObject,
    mut v_a_2693_: *mut LeanObject,
    mut v_a_2694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2695_: *mut LeanObject = core::ptr::null_mut();
    v_res_2695_ =
        l_Lean_Doc_Syntax_metadataContents_formatter(v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
    lean_dec(v_a_2693_);
    lean_dec_ref(v_a_2692_);
    lean_dec(v_a_2691_);
    lean_dec_ref(v_a_2690_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_Doc_Syntax_metadataContents_parenthesizer(
    mut v_a_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    v___x_2710_ = l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2;
    v___x_2711_ = l_Lean_Parser_Term_structInstFields_parenthesizer(
        v___x_2710_,
        v_a_2705_,
        v_a_2706_,
        v_a_2707_,
        v_a_2708_,
    );
    return v___x_2711_;
}
pub unsafe fn l_Lean_Doc_Syntax_metadataContents_parenthesizer___boxed(
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2717_: *mut LeanObject = core::ptr::null_mut();
    v_res_2717_ = l_Lean_Doc_Syntax_metadataContents_parenthesizer(
        v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_,
    );
    lean_dec(v_a_2715_);
    lean_dec_ref(v_a_2714_);
    lean_dec(v_a_2713_);
    lean_dec_ref(v_a_2712_);
    return v_res_2717_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1()
-> *mut LeanObject {
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    v___x_2746_ = l_Lean_Doc_Syntax_command___closed__1;
    v___x_2747_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0;
    v___x_2748_ = l_Lean_addBuiltinDocString(v___x_2746_, v___x_2747_);
    return v___x_2748_;
}
pub unsafe fn l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___boxed(
    mut v_a_2749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2750_: *mut LeanObject = core::ptr::null_mut();
    v_res_2750_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1();
    return v_res_2750_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Category_arg__val = _init_l_Lean_Parser_Category_arg__val();
    lean_mark_persistent(l_Lean_Parser_Category_arg__val);
    l_Lean_Parser_Category_doc__arg = _init_l_Lean_Parser_Category_doc__arg();
    lean_mark_persistent(l_Lean_Parser_Category_doc__arg);
    l_Lean_Parser_Category_link__target = _init_l_Lean_Parser_Category_link__target();
    lean_mark_persistent(l_Lean_Parser_Category_link__target);
    l_Lean_Parser_Category_inline = _init_l_Lean_Parser_Category_inline();
    lean_mark_persistent(l_Lean_Parser_Category_inline);
    l_Lean_Parser_Category_block = _init_l_Lean_Parser_Category_block();
    lean_mark_persistent(l_Lean_Parser_Category_block);
    l_Lean_Parser_Category_list__item = _init_l_Lean_Parser_Category_list__item();
    lean_mark_persistent(l_Lean_Parser_Category_list__item);
    l_Lean_Parser_Category_desc__item = _init_l_Lean_Parser_Category_desc__item();
    lean_mark_persistent(l_Lean_Parser_Category_desc__item);
    l_Lean_Doc_Syntax_metadataContents = _init_l_Lean_Doc_Syntax_metadataContents();
    lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DocString_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Term_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_DocString_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_DocString_Syntax(builtin);
}
