// Lean compiler output
// Module: Init.Conv
// Imports: Init.Tactics Init.Meta
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Parser_Tactic_getConfigItems;
use crate::r#gen::Init::Meta::{initialize_Init_Meta, meta_initialize_Init_Meta};
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value)
                as *mut LeanObject,
            5855146430765573009 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value: LeanStringObject<5> =
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
        m_data: [99, 111, 110, 118, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
                as *mut LeanObject,
            5852136541633594344 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__3_value)
                as *mut LeanObject,
            2853200300723924294 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value: LeanStringObject<8> =
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__7_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
                as *mut LeanObject,
            5852136541633594344 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__11_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value: LeanStringObject<2> =
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
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__6_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_quot___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_conv_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__18_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_conv: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value: LeanStringObject<17> =
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
            99, 111, 110, 118, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value: LeanStringObject<5> =
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
        m_data: [67, 111, 110, 118, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value)
                as *mut LeanObject,
            2194001538128159737 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            115, 101, 112, 66, 121, 49, 73, 110, 100, 101, 110, 116, 83, 101, 109, 105, 99, 111,
            108, 111, 110, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__4_value)
                as *mut LeanObject,
            12439213008700076310 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convSeq1Indented: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value: LeanStringObject<17> =
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
            99, 111, 110, 118, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value)
                as *mut LeanObject,
            4863285515324763763 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value: LeanStringObject<2> =
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
        m_data: [123, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value: LeanStringObject<16> =
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
            119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__4_value)
                as *mut LeanObject,
            1164644006045091397 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            115, 101, 112, 66, 121, 73, 110, 100, 101, 110, 116, 83, 101, 109, 105, 99, 111, 108,
            111, 110, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__6_value)
                as *mut LeanObject,
            8450841259565682059 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value: LeanStringObject<2> =
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
        m_data: [125, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convSeqBracketed: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value: LeanStringObject<8> =
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
        m_data: [99, 111, 110, 118, 83, 101, 113, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value)
                as *mut LeanObject,
            4619875164071285194 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value: LeanStringObject<7> =
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
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__2_value)
                as *mut LeanObject,
            393173242845875278 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convSeq___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convSeq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value: LeanStringObject<13> =
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
        m_data: [111, 99, 99, 115, 87, 105, 108, 100, 99, 97, 114, 100, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value)
                as *mut LeanObject,
            11436923668760528595 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value: LeanStringObject<2> =
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
        m_data: [42, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_occsWildcard: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value: LeanStringObject<12> =
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
        m_data: [111, 99, 99, 115, 73, 110, 100, 101, 120, 101, 100, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value)
                as *mut LeanObject,
            10410387794395025201 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value: LeanStringObject<6> =
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
        m_data: [109, 97, 110, 121, 49, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__2_value)
                as *mut LeanObject,
            17243740965612849207 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value: LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__4_value)
                as *mut LeanObject,
            6110315075117401315 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_occsIndexed: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__0_value: LeanStringObject<5> =
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
        m_data: [111, 99, 99, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_occs___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__0_value) as *mut LeanObject,
        3133829275317851260 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__2_value: LeanStringObject<7> =
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
        m_data: [97, 116, 111, 109, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__2_value) as *mut LeanObject,
        4024150434455327032 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__4_value: LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__9_value: LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__10_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsWildcard___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__8_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__14_value: LeanStringObject<3> =
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
        m_data: [41, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_occs___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__15_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_occs___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 9,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_occs___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__17_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_occs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value: LeanStringObject<18> =
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
            119, 105, 116, 104, 65, 110, 110, 111, 116, 97, 116, 101, 83, 116, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__0_value)
                as *mut LeanObject,
            3238020878805402882 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            119, 105, 116, 104, 95, 97, 110, 110, 111, 116, 97, 116, 101, 95, 115, 116, 97, 116,
            101, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value: LeanStringObject<7> =
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
        m_data: [114, 97, 119, 83, 116, 120, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__4_value)
                as *mut LeanObject,
            7922007774678457419 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__5_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value: LeanStringObject<8> =
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
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__8_value)
                as *mut LeanObject,
            17761616517784022991 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_withAnnotateState: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_skip___closed__0_value: LeanStringObject<5> =
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
        m_data: [115, 107, 105, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_skip___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_skip___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__0_value) as *mut LeanObject,
        13842034534476526597 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_skip___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_skip___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_skip___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_skip___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_skip___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_skip: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_skip___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_cbv___closed__0_value: LeanStringObject<4> =
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
        m_data: [99, 98, 118, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_cbv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_cbv___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__0_value) as *mut LeanObject,
        12057338954073742905 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_cbv___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_cbv___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_cbv___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_cbv___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_cbv___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_cbv: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_cbv___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_lhs___closed__0_value: LeanStringObject<4> =
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
        m_data: [108, 104, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_lhs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_lhs___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__0_value) as *mut LeanObject,
        2383240203624611278 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_lhs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_lhs___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_lhs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_lhs___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_lhs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_lhs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_lhs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rhs___closed__0_value: LeanStringObject<4> =
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
        m_data: [114, 104, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_rhs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_rhs___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__0_value) as *mut LeanObject,
        14493188234565044157 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_rhs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rhs___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_rhs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rhs___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_rhs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_rhs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rhs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_fun___closed__0_value: LeanStringObject<4> =
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
        m_data: [102, 117, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_fun___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_fun___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__0_value) as *mut LeanObject,
        14856247777542608561 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_fun___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_fun___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_fun___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_fun___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_fun___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_fun: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_fun___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_whnf___closed__0_value: LeanStringObject<5> =
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
        m_data: [119, 104, 110, 102, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_whnf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_whnf___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__0_value) as *mut LeanObject,
        5293136351122059060 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_whnf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_whnf___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_whnf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_whnf___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_whnf___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_whnf: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_whnf___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_zeta___closed__0_value: LeanStringObject<5> =
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
        m_data: [122, 101, 116, 97, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_zeta___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_zeta___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__0_value) as *mut LeanObject,
        2162740105087520528 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_zeta___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_zeta___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_zeta___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_zeta___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_zeta___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_zeta: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_zeta___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_reduce___closed__0_value: LeanStringObject<7> =
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
        m_data: [114, 101, 100, 117, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_reduce___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_reduce___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__0_value) as *mut LeanObject,
        7650338142865358823 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_reduce___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_reduce___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_reduce___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_reduce___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_reduce___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_reduce: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_reduce___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_congr___closed__0_value: LeanStringObject<6> =
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
        m_data: [99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_congr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_congr___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__0_value) as *mut LeanObject,
        14427030059196397072 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_congr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_congr___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_congr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_congr___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_congr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_congr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_congr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__0_value: LeanStringObject<7> =
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
        m_data: [97, 114, 103, 65, 114, 103, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__0_value) as *mut LeanObject,
        9815751759067206459 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__2_value: LeanStringObject<9> =
    LeanStringObject {
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
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__2_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__4_value: LeanStringObject<2> =
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
        m_data: [64, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__7_value: LeanStringObject<2> =
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
        m_data: [45, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_argArg___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_argArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_argArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__0_value: LeanStringObject<4> =
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
        m_data: [97, 114, 103, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_arg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_arg___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__0_value) as *mut LeanObject,
        6940441580804063122 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_arg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__2_value: LeanStringObject<5> =
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
        m_data: [97, 114, 103, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_arg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_arg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_arg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_arg___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_arg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_arg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_arg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__0_value: LeanStringObject<4> =
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
        m_data: [101, 120, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_ext___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__0_value) as *mut LeanObject,
        5818266883322100681 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__3_value: LeanStringObject<5> =
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
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__3_value) as *mut LeanObject,
        2302572775315350313 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__5_value: LeanStringObject<6> =
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
        m_data: [99, 111, 108, 71, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_ext___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__5_value) as *mut LeanObject,
        17597206043415342265 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_ext___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__8_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_ext___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_ext___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_ext___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_ext___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_ext___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_ext: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_change___closed__0_value: LeanStringObject<7> =
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
        m_data: [99, 104, 97, 110, 103, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_change___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__0_value) as *mut LeanObject,
        1203263152968118357 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_change___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__2_value: LeanStringObject<8> =
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
        m_data: [99, 104, 97, 110, 103, 101, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_change___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__4_value: LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_change___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__4_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_change___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__5_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_change___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_change___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_change___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_change___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_change: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__0_value: LeanStringObject<6> =
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
        m_data: [100, 101, 108, 116, 97, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_delta___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__0_value) as *mut LeanObject,
        8745909130110294463 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_delta___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_delta___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__3_value: LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_delta___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__3_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_delta___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_delta___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_delta___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_delta___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_delta___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_delta___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_delta___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_delta: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__0_value: LeanStringObject<7> =
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
        m_data: [117, 110, 102, 111, 108, 100, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__0_value) as *mut LeanObject,
        14363068710658641377 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_unfold___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_unfold___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_unfold: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_unfold___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__0_value: LeanStringObject<8> =
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
        m_data: [112, 97, 116, 116, 101, 114, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__0_value)
                as *mut LeanObject,
            3861856325106436923 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_pattern___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_pattern___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_pattern: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value: LeanStringObject<8> =
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
        m_data: [114, 101, 119, 114, 105, 116, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value)
                as *mut LeanObject,
            779923751473675077 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_rewrite___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_rewrite___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_rewrite___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_rewrite: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__0_value: LeanStringObject<5> =
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
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_simp___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__0_value) as *mut LeanObject,
        14621726445050439147 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__6_value: LeanStringObject<6> =
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
        m_data: [32, 111, 110, 108, 121, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__6_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__8_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__10_value: LeanStringObject<3> =
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
        m_data: [32, 91, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__11_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__11_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__14_value: LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__15_value: LeanStringObject<3> =
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
static mut l_Lean_Parser_Tactic_Conv_simp___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__16_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__16_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simp___closed__20_value: LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simp___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simp___closed__21_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__20_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__21_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simp___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simp___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simp___closed__25: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_simp: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value: LeanStringObject<10> =
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
        m_data: [115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__0_value)
                as *mut LeanObject,
            4033974689118230740 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value: LeanStringObject<6> =
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
        m_data: [115, 105, 109, 112, 63, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpTrace___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_simpTrace___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_simpTrace: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value: LeanStringObject<6> =
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
        m_data: [100, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value) as *mut LeanObject,
        682381425026147175 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_dsimp___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimp___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimp___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_dsimp: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value: LeanStringObject<11> =
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
        m_data: [100, 115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__0_value)
                as *mut LeanObject,
            1408925737459485508 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value: LeanStringObject<7> =
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
        m_data: [100, 115, 105, 109, 112, 63, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_dsimpTrace: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value: LeanStringObject<10> =
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
        m_data: [115, 105, 109, 112, 77, 97, 116, 99, 104, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__0_value)
                as *mut LeanObject,
            2709596213829771159 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value: LeanStringObject<11> =
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
        m_data: [115, 105, 109, 112, 95, 109, 97, 116, 99, 104, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_simpMatch___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_simpMatch: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simpMatch___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__0_value: LeanStringObject<6> =
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
        m_data: [99, 108, 101, 97, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_clear___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_clear___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__0_value) as *mut LeanObject,
        12526317070040649423 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_clear___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_clear___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__5_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_clear___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_clear___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_clear___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_clear___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_clear___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_clear___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__7_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_clear: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_clear___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value: LeanStringObject<17> =
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
            110, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 67, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__0_value)
                as *mut LeanObject,
            14672341133913102249 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value: LeanStringObject<8> =
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
        m_data: [116, 97, 99, 116, 105, 99, 39, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value: LeanStringObject<5> =
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
        m_data: [32, 61, 62, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value: LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value)
                as *mut LeanObject,
            11103865283154438669 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_nestedTacticCore: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value: LeanStringObject<13> =
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
        m_data: [110, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__0_value)
                as *mut LeanObject,
            9934668988201376792 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value: LeanStringObject<7> =
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
        m_data: [116, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_nestedTactic: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTactic___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value: LeanStringObject<11> =
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
        m_data: [99, 111, 110, 118, 84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__0_value)
                as *mut LeanObject,
            3529167016356999086 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value: LeanStringObject<6> =
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
        m_data: [99, 111, 110, 118, 39, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTactic___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convTactic: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTactic___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value: LeanStringObject<11> =
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
        m_data: [110, 101, 115, 116, 101, 100, 67, 111, 110, 118, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedConv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__0_value)
                as *mut LeanObject,
            13793888648781409952 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedConv___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_nestedConv___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_nestedConv: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedConv___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__0_value: LeanStringObject<6> =
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
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_paren___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_paren___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__0_value) as *mut LeanObject,
        4160726102902615044 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_paren___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occs___closed__4_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_paren___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_paren___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_paren___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__14_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_paren___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_paren___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_paren___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_paren: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value: LeanStringObject<8> =
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
        m_data: [99, 111, 110, 118, 82, 102, 108, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__0_value)
                as *mut LeanObject,
            5675369482127682097 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value: LeanStringObject<4> =
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
        m_data: [114, 102, 108, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRfl___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convRfl: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRfl___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__7_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__2_value) as *mut LeanObject,17228437386856258271 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__4_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__6_value) as *mut LeanObject,3294379458557754569 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__0_value)
                as *mut LeanObject,
            11329495071494069401 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__2_value: LeanStringObject<5> =
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
        m_data: [100, 111, 110, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convDone___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convDone___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convDone: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__4_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convDone___closed__2_value) as *mut LeanObject,8876691400619696497 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value: LeanStringObject<16> =
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
            99, 111, 110, 118, 84, 114, 97, 99, 101, 95, 115, 116, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__0_value)
                as *mut LeanObject,
            5453012680849693201 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value: LeanStringObject<12> =
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
        m_data: [116, 114, 97, 99, 101, 95, 115, 116, 97, 116, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convTrace__state: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTrace__state___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 114, 97, 99, 101, 83, 116, 97, 116, 101, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__0_value) as *mut LeanObject,14912751384704677824 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value)
                as *mut LeanObject,
            1113262671135127376 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value: LeanStringObject<11> =
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
        m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_allGoals___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_allGoals: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__5_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_allGoals___closed__0_value) as *mut LeanObject,14131640301685195369 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value)
                as *mut LeanObject,
            17733550178357422433 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value: LeanStringObject<11> =
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
        m_data: [97, 110, 121, 95, 103, 111, 97, 108, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_anyGoals___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_anyGoals: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__5_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_anyGoals___closed__0_value) as *mut LeanObject,2355218674864034728 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 110, 121, 95, 103, 111, 97, 108, 115, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__0_value: LeanStringObject<5> =
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
        m_data: [99, 97, 115, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_case___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__0_value) as *mut LeanObject,
        11752510286238259185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_case___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__2_value: LeanStringObject<6> =
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
        m_data: [99, 97, 115, 101, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_case___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__4_value: LeanStringObject<2> =
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
        m_data: [124, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_case___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__5_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_case___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_case: *mut LeanObject = core::ptr::null_mut();
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case___closed__0_value) as *mut LeanObject,3714280620155270360 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value: LeanStringObject<6> =
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
        m_data: [99, 97, 115, 101, 39, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value)
                as *mut LeanObject,
            2260385614914559383 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value: LeanStringObject<7> =
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
        m_data: [99, 97, 115, 101, 39, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_case_x27___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_case_x27___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_case_x27: *mut LeanObject = core::ptr::null_mut();
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_case_x27___closed__0_value) as *mut LeanObject,7640173075534255494 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value: LeanStringObject<
    14,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_3: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__0_value
            ) as *mut LeanObject,
            3719486818457681805 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__2_value
            ) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__0_value) as *mut LeanObject,13771926289831477797 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 65, 114, 103, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__2_value) as *mut LeanObject,14546932361418667927 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value) as *mut LeanObject,3984140175429830279 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__0_value: LeanStringObject<6> =
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
        m_data: [102, 111, 99, 117, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_focus___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_focus___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__0_value) as *mut LeanObject,
        14932297365852547287 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_focus___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__2_value: LeanStringObject<7> =
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
        m_data: [102, 111, 99, 117, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_focus___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_focus___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_focus___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_focus___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_focus___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_focus: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__5_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_focus___closed__0_value) as *mut LeanObject,15976019963061198790 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value: LeanStringObject<12> =
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
        m_data: [99, 111, 110, 118, 67, 111, 110, 118, 83, 101, 113, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__0_value)
                as *mut LeanObject,
            18300610594507675016 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convConvSeq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__0_value)
                as *mut LeanObject,
            14887932109376590136 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value: LeanStringObject<3> =
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
        m_data: [46, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 12,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__3_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_conv_xb7__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value: LeanStringObject<14> =
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
            102, 97, 105, 108, 73, 102, 83, 117, 99, 99, 101, 115, 115, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value)
                as *mut LeanObject,
            6792037844894501418 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value: LeanStringObject<17> =
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
            102, 97, 105, 108, 95, 105, 102, 95, 115, 117, 99, 99, 101, 115, 115, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_failIfSuccess: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__5_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__0_value) as *mut LeanObject,17788448959859761123 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [102, 97, 105, 108, 95, 105, 102, 95, 115, 117, 99, 99, 101, 115, 115, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__0_value)
                as *mut LeanObject,
            1169967066955421272 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value: LeanStringObject<3> =
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
        m_data: [114, 119, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_convRw____: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value: LeanStringObject<10> =
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
        m_data: [99, 111, 110, 118, 69, 114, 119, 95, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__0_value)
                as *mut LeanObject,
            871072607707394147 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value: LeanStringObject<4> =
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
        m_data: [101, 114, 119, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_convErw____: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__0_value) as *mut LeanObject,3488656302031949961 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__2_value) as *mut LeanObject,10138443044734372301 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__4_value) as *mut LeanObject,13577612981047608199 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6_value) as *mut LeanObject,9886976150145685689 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__10_value) as *mut LeanObject,14183307858573822893 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value) as *mut LeanObject,9666231177748665885 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__16_value) as *mut LeanObject,13340093926952294564 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13_value) as *mut LeanObject,609174137020324014 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__17_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15_value) as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__19_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__18_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__20_value) as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__0_value)
                as *mut LeanObject,
            8815029478349537649 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value: LeanStringObject<5> =
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
        m_data: [97, 114, 103, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convArgs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convArgs: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convArgs___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__0_value)
                as *mut LeanObject,
            5744455334158526087 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value: LeanStringObject<5> =
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
        m_data: [108, 101, 102, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convLeft___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convLeft: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convLeft___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__0_value: LeanStringObject<10> =
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
        m_data: [99, 111, 110, 118, 82, 105, 103, 104, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__0_value)
                as *mut LeanObject,
            10406812282498978092 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__2_value: LeanStringObject<6> =
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
        m_data: [114, 105, 103, 104, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRight___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRight___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convRight: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRight___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value: LeanStringObject<13> =
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
        m_data: [99, 111, 110, 118, 73, 110, 116, 114, 111, 95, 95, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__0_value)
                as *mut LeanObject,
            4938971775571215549 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value: LeanStringObject<6> =
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
        m_data: [105, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_convIntro______: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value: LeanStringObject<13> =
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
        m_data: [101, 110, 116, 101, 114, 80, 97, 116, 116, 101, 114, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value)
                as *mut LeanObject,
            7552558446830534184 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value: LeanStringObject<4> =
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
        m_data: [105, 110, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterPattern___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_enterPattern: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__0_value)
                as *mut LeanObject,
            7908174979996395449 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enterArg___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterPattern___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enterArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_enterArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_enterArg: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_enter___closed__0_value: LeanStringObject<6> =
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
        m_data: [101, 110, 116, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_enter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_enter___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__0_value) as *mut LeanObject,
        7814780372252873783 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_enter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enter___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_enter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_enter___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_simp___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_enter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_enter___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_enter___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_enter___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enter___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_enter___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enter___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_enter___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enter___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_enter___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_enter___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_enter___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_enter: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value: LeanStringObject<11> =
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
        m_data: [99, 111, 110, 118, 65, 112, 112, 108, 121, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__0_value)
                as *mut LeanObject,
            6570134606486243148 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value: LeanStringObject<7> =
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
        m_data: [97, 112, 112, 108, 121, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convApply___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convApply__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convApply___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0_value) as *mut LeanObject,5826123769708379594 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__0_value: LeanStringObject<6> =
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
        m_data: [102, 105, 114, 115, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_first___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__0_value) as *mut LeanObject,
        17591797804533379362 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__2_value: LeanStringObject<7> =
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
        m_data: [102, 105, 114, 115, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__4_value: LeanStringObject<13> =
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
        m_data: [119, 105, 116, 104, 80, 111, 115, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__4_value) as *mut LeanObject,
        17180264478054591478 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__6_value: LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__6_value) as *mut LeanObject,
        2214559063752339918 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__8_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_first___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__8_value) as *mut LeanObject,
        2710995909225096690 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__10_value: LeanStringObject<7> =
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
        m_data: [112, 112, 76, 105, 110, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__10_value) as *mut LeanObject,
        4227538229121138037 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__12_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__14_value: LeanStringObject<6> =
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
        m_data: [99, 111, 108, 71, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__14_value) as *mut LeanObject,
        4942254933594350711 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__16_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__18_value: LeanStringObject<3> =
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
        m_data: [124, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_first___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__18_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__19_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__18_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__19_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__20_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__17_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__20_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__21_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__20_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__21_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__22_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__21_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__22_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__23_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_occsIndexed___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__22_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__23_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__24_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__23_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__24_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__25_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__24_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__25_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_first___closed__26_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__25_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_first___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__26_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_first: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_first___closed__26_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__0_value)
                as *mut LeanObject,
            15272911930721002417 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value: LeanStringObject<5> =
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
        m_data: [116, 114, 121, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convTry___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convTry__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convTry___00__closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__0_value)
                as *mut LeanObject,
            2841688605323704715 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value: LeanStringObject<6> =
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
        m_data: [32, 60, 59, 62, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__0_value) as *mut LeanObject,12695378809397736991 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_paren___closed__0_value) as *mut LeanObject,8689124066155232629 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 59, 62, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value: LeanStringObject<12> =
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
        m_data: [99, 111, 110, 118, 82, 101, 112, 101, 97, 116, 95, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__0_value)
                as *mut LeanObject,
            14131562680861795865 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value: LeanStringObject<8> =
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
        m_data: [114, 101, 112, 101, 97, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_convRepeat__: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 112, 101, 97, 116, 0]};
static mut l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value: LeanStringObject<12> =
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
        m_data: [101, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__0_value)
                as *mut LeanObject,
            3123354491248406356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value: LeanStringObject<14> =
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
            101, 120, 116, 114, 97, 99, 116, 95, 108, 101, 116, 115, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__4_value) as *mut LeanObject,6287085762317100023 as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__8_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_extractLets___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_ext___closed__4_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_extractLets___closed__9_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_extractLets___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_extractLets: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__0_value)
                as *mut LeanObject,
            15211363250062378073 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value: LeanStringObject<11> =
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
        m_data: [108, 105, 102, 116, 95, 108, 101, 116, 115, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_liftLets___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_liftLets___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_Conv_liftLets___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_Conv_liftLets: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value: LeanStringObject<10> =
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
        m_data: [108, 101, 116, 84, 111, 72, 97, 118, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__0_value)
                as *mut LeanObject,
            1576434579341158445 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value: LeanStringObject<12> =
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
        m_data: [108, 101, 116, 95, 116, 111, 95, 104, 97, 118, 101, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_letToHave___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_letToHave: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_letToHave___closed__4_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
            as *mut LeanObject,
        2622230176999461939 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_Conv_conv___closed__0_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__5_value)
            as *mut LeanObject,
        8265518440499324864 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__1_value: LeanStringObject<5> =
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
        m_data: [32, 97, 116, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__2_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_delta___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convConvSeq___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__6_value: LeanStringObject<5> =
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
        m_data: [32, 105, 110, 32, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_conv___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_pattern___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_change___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_argArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_conv___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__0_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_Conv_conv___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__14_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_conv: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_conv_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__2_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__0_value)
                as *mut LeanObject,
            5411934985460699852 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__2_value: LeanStringObject<10> =
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
        m_data: [110, 111, 114, 109, 95, 99, 97, 115, 116, 0],
    };
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__2_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_Conv_normCast___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_Conv_normCast___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_Conv_normCast: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_Conv_normCast___closed__4_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_Category_conv() -> *mut LeanObject {
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    v___x_2751_ = lean_box(0);
    return v___x_2751_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext___closed__9() -> *mut LeanObject {
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Lean_binderIdent;
    v___x_3169_ = l_Lean_Parser_Tactic_Conv_ext___closed__8;
    v___x_3170_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3171_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3171_, 0, v___x_3170_);
    lean_ctor_set(v___x_3171_, 1, v___x_3169_);
    lean_ctor_set(v___x_3171_, 2, v___x_3168_);
    return v___x_3171_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext___closed__10() -> *mut LeanObject {
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    v___x_3172_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__9,
    );
    v___x_3173_ = l_Lean_Parser_Tactic_Conv_ext___closed__4;
    v___x_3174_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3174_, 0, v___x_3173_);
    lean_ctor_set(v___x_3174_, 1, v___x_3172_);
    return v___x_3174_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext___closed__11() -> *mut LeanObject {
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    v___x_3175_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__10,
    );
    v___x_3176_ = l_Lean_Parser_Tactic_Conv_ext___closed__2;
    v___x_3177_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3178_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3178_, 0, v___x_3177_);
    lean_ctor_set(v___x_3178_, 1, v___x_3176_);
    lean_ctor_set(v___x_3178_, 2, v___x_3175_);
    return v___x_3178_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext___closed__12() -> *mut LeanObject {
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    v___x_3179_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__11_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__11,
    );
    v___x_3180_ = lean_unsigned_to_nat(1022);
    v___x_3181_ = l_Lean_Parser_Tactic_Conv_ext___closed__1;
    v___x_3182_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3182_, 0, v___x_3181_);
    lean_ctor_set(v___x_3182_, 1, v___x_3180_);
    lean_ctor_set(v___x_3182_, 2, v___x_3179_);
    return v___x_3182_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_ext() -> *mut LeanObject {
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    v___x_3183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__12_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__12,
    );
    return v___x_3183_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__3() -> *mut LeanObject {
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    v___x_3297_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3298_ = l_Lean_Parser_Tactic_Conv_rewrite___closed__2;
    v___x_3299_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3300_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3300_, 0, v___x_3299_);
    lean_ctor_set(v___x_3300_, 1, v___x_3298_);
    lean_ctor_set(v___x_3300_, 2, v___x_3297_);
    return v___x_3300_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__4() -> *mut LeanObject {
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lean_Parser_Tactic_rwRuleSeq;
    v___x_3302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__3_once),
        _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__3,
    );
    v___x_3303_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3304_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3304_, 0, v___x_3303_);
    lean_ctor_set(v___x_3304_, 1, v___x_3302_);
    lean_ctor_set(v___x_3304_, 2, v___x_3301_);
    return v___x_3304_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__5() -> *mut LeanObject {
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    v___x_3305_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__4,
    );
    v___x_3306_ = lean_unsigned_to_nat(1022);
    v___x_3307_ = l_Lean_Parser_Tactic_Conv_rewrite___closed__1;
    v___x_3308_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3308_, 0, v___x_3307_);
    lean_ctor_set(v___x_3308_, 1, v___x_3306_);
    lean_ctor_set(v___x_3308_, 2, v___x_3305_);
    return v___x_3308_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_rewrite() -> *mut LeanObject {
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    v___x_3309_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_rewrite___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_rewrite___closed__5,
    );
    return v___x_3309_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__3() -> *mut LeanObject {
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3321_ = l_Lean_Parser_Tactic_Conv_simp___closed__2;
    v___x_3322_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3323_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3323_, 0, v___x_3322_);
    lean_ctor_set(v___x_3323_, 1, v___x_3321_);
    lean_ctor_set(v___x_3323_, 2, v___x_3320_);
    return v___x_3323_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__4() -> *mut LeanObject {
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Lean_Parser_Tactic_discharger;
    v___x_3325_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3326_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3326_, 0, v___x_3325_);
    lean_ctor_set(v___x_3326_, 1, v___x_3324_);
    return v___x_3326_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__5() -> *mut LeanObject {
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    v___x_3327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__4,
    );
    v___x_3328_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__3_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__3,
    );
    v___x_3329_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3330_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3330_, 0, v___x_3329_);
    lean_ctor_set(v___x_3330_, 1, v___x_3328_);
    lean_ctor_set(v___x_3330_, 2, v___x_3327_);
    return v___x_3330_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__9() -> *mut LeanObject {
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    v___x_3338_ = l_Lean_Parser_Tactic_Conv_simp___closed__8;
    v___x_3339_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__5,
    );
    v___x_3340_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3341_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3341_, 0, v___x_3340_);
    lean_ctor_set(v___x_3341_, 1, v___x_3339_);
    lean_ctor_set(v___x_3341_, 2, v___x_3338_);
    return v___x_3341_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__12() -> *mut LeanObject {
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Lean_Parser_Tactic_simpLemma;
    v___x_3346_ = l_Lean_Parser_Tactic_simpErase;
    v___x_3347_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__3;
    v___x_3348_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3348_, 0, v___x_3347_);
    lean_ctor_set(v___x_3348_, 1, v___x_3346_);
    lean_ctor_set(v___x_3348_, 2, v___x_3345_);
    return v___x_3348_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__13() -> *mut LeanObject {
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    v___x_3349_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__12_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__12,
    );
    v___x_3350_ = l_Lean_Parser_Tactic_simpStar;
    v___x_3351_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__3;
    v___x_3352_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3352_, 0, v___x_3351_);
    lean_ctor_set(v___x_3352_, 1, v___x_3350_);
    lean_ctor_set(v___x_3352_, 2, v___x_3349_);
    return v___x_3352_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__17() -> *mut LeanObject {
    let mut v___x_3357_: u8 = 0;
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    v___x_3357_ = 0;
    v___x_3358_ = l_Lean_Parser_Tactic_Conv_simp___closed__16;
    v___x_3359_ = l_Lean_Parser_Tactic_Conv_simp___closed__14;
    v___x_3360_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__13_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__13,
    );
    v___x_3361_ = lean_alloc_ctor(10, 3, (1) as u32);
    lean_ctor_set(v___x_3361_, 0, v___x_3360_);
    lean_ctor_set(v___x_3361_, 1, v___x_3359_);
    lean_ctor_set(v___x_3361_, 2, v___x_3358_);
    lean_ctor_set_uint8(
        v___x_3361_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3357_,
    );
    return v___x_3361_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__18() -> *mut LeanObject {
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    v___x_3362_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__17_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__17,
    );
    v___x_3363_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5;
    v___x_3364_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3364_, 0, v___x_3363_);
    lean_ctor_set(v___x_3364_, 1, v___x_3362_);
    return v___x_3364_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__19() -> *mut LeanObject {
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    v___x_3365_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__18_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__18,
    );
    v___x_3366_ = l_Lean_Parser_Tactic_Conv_simp___closed__11;
    v___x_3367_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3368_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3368_, 0, v___x_3367_);
    lean_ctor_set(v___x_3368_, 1, v___x_3366_);
    lean_ctor_set(v___x_3368_, 2, v___x_3365_);
    return v___x_3368_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__22() -> *mut LeanObject {
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    v___x_3372_ = l_Lean_Parser_Tactic_Conv_simp___closed__21;
    v___x_3373_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__19_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__19,
    );
    v___x_3374_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3375_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3375_, 0, v___x_3374_);
    lean_ctor_set(v___x_3375_, 1, v___x_3373_);
    lean_ctor_set(v___x_3375_, 2, v___x_3372_);
    return v___x_3375_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__23() -> *mut LeanObject {
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    v___x_3376_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__22_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__22,
    );
    v___x_3377_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3378_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3378_, 0, v___x_3377_);
    lean_ctor_set(v___x_3378_, 1, v___x_3376_);
    return v___x_3378_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__24() -> *mut LeanObject {
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    v___x_3379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__23_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__23,
    );
    v___x_3380_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__9,
    );
    v___x_3381_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3382_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3382_, 0, v___x_3381_);
    lean_ctor_set(v___x_3382_, 1, v___x_3380_);
    lean_ctor_set(v___x_3382_, 2, v___x_3379_);
    return v___x_3382_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp___closed__25() -> *mut LeanObject {
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    v___x_3383_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__24_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__24,
    );
    v___x_3384_ = lean_unsigned_to_nat(1022);
    v___x_3385_ = l_Lean_Parser_Tactic_Conv_simp___closed__1;
    v___x_3386_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3386_, 0, v___x_3385_);
    lean_ctor_set(v___x_3386_, 1, v___x_3384_);
    lean_ctor_set(v___x_3386_, 2, v___x_3383_);
    return v___x_3386_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simp() -> *mut LeanObject {
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    v___x_3387_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__25_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__25,
    );
    return v___x_3387_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__4() -> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3400_ = l_Lean_Parser_Tactic_Conv_simpTrace___closed__3;
    v___x_3401_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3402_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3402_, 0, v___x_3401_);
    lean_ctor_set(v___x_3402_, 1, v___x_3400_);
    lean_ctor_set(v___x_3402_, 2, v___x_3399_);
    return v___x_3402_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__5() -> *mut LeanObject {
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    v___x_3403_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__4,
    );
    v___x_3404_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__4,
    );
    v___x_3405_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3406_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3406_, 0, v___x_3405_);
    lean_ctor_set(v___x_3406_, 1, v___x_3404_);
    lean_ctor_set(v___x_3406_, 2, v___x_3403_);
    return v___x_3406_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__6() -> *mut LeanObject {
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_Parser_Tactic_Conv_simp___closed__8;
    v___x_3408_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__5,
    );
    v___x_3409_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3410_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3410_, 0, v___x_3409_);
    lean_ctor_set(v___x_3410_, 1, v___x_3408_);
    lean_ctor_set(v___x_3410_, 2, v___x_3407_);
    return v___x_3410_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__7() -> *mut LeanObject {
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    v___x_3411_ = l_Lean_Parser_Tactic_simpArgs;
    v___x_3412_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3413_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3413_, 0, v___x_3412_);
    lean_ctor_set(v___x_3413_, 1, v___x_3411_);
    return v___x_3413_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__8() -> *mut LeanObject {
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3414_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__7,
    );
    v___x_3415_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__6,
    );
    v___x_3416_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3417_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3417_, 0, v___x_3416_);
    lean_ctor_set(v___x_3417_, 1, v___x_3415_);
    lean_ctor_set(v___x_3417_, 2, v___x_3414_);
    return v___x_3417_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__9() -> *mut LeanObject {
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    v___x_3418_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__8,
    );
    v___x_3419_ = lean_unsigned_to_nat(1022);
    v___x_3420_ = l_Lean_Parser_Tactic_Conv_simpTrace___closed__1;
    v___x_3421_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3421_, 0, v___x_3420_);
    lean_ctor_set(v___x_3421_, 1, v___x_3419_);
    lean_ctor_set(v___x_3421_, 2, v___x_3418_);
    return v___x_3421_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_simpTrace() -> *mut LeanObject {
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    v___x_3422_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simpTrace___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_simpTrace___closed__9,
    );
    return v___x_3422_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__3() -> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3434_ = l_Lean_Parser_Tactic_Conv_dsimp___closed__2;
    v___x_3435_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3436_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3436_, 0, v___x_3435_);
    lean_ctor_set(v___x_3436_, 1, v___x_3434_);
    lean_ctor_set(v___x_3436_, 2, v___x_3433_);
    return v___x_3436_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__4() -> *mut LeanObject {
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3437_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__4,
    );
    v___x_3438_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__3_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__3,
    );
    v___x_3439_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3440_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3440_, 0, v___x_3439_);
    lean_ctor_set(v___x_3440_, 1, v___x_3438_);
    lean_ctor_set(v___x_3440_, 2, v___x_3437_);
    return v___x_3440_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__5() -> *mut LeanObject {
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    v___x_3441_ = l_Lean_Parser_Tactic_Conv_simp___closed__8;
    v___x_3442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__4,
    );
    v___x_3443_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3444_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3444_, 0, v___x_3443_);
    lean_ctor_set(v___x_3444_, 1, v___x_3442_);
    lean_ctor_set(v___x_3444_, 2, v___x_3441_);
    return v___x_3444_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__6() -> *mut LeanObject {
    let mut v___x_3445_: u8 = 0;
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    v___x_3445_ = 0;
    v___x_3446_ = l_Lean_Parser_Tactic_Conv_simp___closed__16;
    v___x_3447_ = l_Lean_Parser_Tactic_Conv_simp___closed__14;
    v___x_3448_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_simp___closed__12_once),
        _init_l_Lean_Parser_Tactic_Conv_simp___closed__12,
    );
    v___x_3449_ = lean_alloc_ctor(10, 3, (1) as u32);
    lean_ctor_set(v___x_3449_, 0, v___x_3448_);
    lean_ctor_set(v___x_3449_, 1, v___x_3447_);
    lean_ctor_set(v___x_3449_, 2, v___x_3446_);
    lean_ctor_set_uint8(
        v___x_3449_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3445_,
    );
    return v___x_3449_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__7() -> *mut LeanObject {
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    v___x_3450_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__6,
    );
    v___x_3451_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5;
    v___x_3452_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3452_, 0, v___x_3451_);
    lean_ctor_set(v___x_3452_, 1, v___x_3450_);
    return v___x_3452_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__8() -> *mut LeanObject {
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    v___x_3453_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__7,
    );
    v___x_3454_ = l_Lean_Parser_Tactic_Conv_simp___closed__11;
    v___x_3455_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3456_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3456_, 0, v___x_3455_);
    lean_ctor_set(v___x_3456_, 1, v___x_3454_);
    lean_ctor_set(v___x_3456_, 2, v___x_3453_);
    return v___x_3456_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__9() -> *mut LeanObject {
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    v___x_3457_ = l_Lean_Parser_Tactic_Conv_simp___closed__21;
    v___x_3458_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__8,
    );
    v___x_3459_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3460_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3460_, 0, v___x_3459_);
    lean_ctor_set(v___x_3460_, 1, v___x_3458_);
    lean_ctor_set(v___x_3460_, 2, v___x_3457_);
    return v___x_3460_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__10() -> *mut LeanObject {
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    v___x_3461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__9,
    );
    v___x_3462_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3463_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3463_, 0, v___x_3462_);
    lean_ctor_set(v___x_3463_, 1, v___x_3461_);
    return v___x_3463_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__11() -> *mut LeanObject {
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    v___x_3464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__10,
    );
    v___x_3465_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__5,
    );
    v___x_3466_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3467_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3467_, 0, v___x_3466_);
    lean_ctor_set(v___x_3467_, 1, v___x_3465_);
    lean_ctor_set(v___x_3467_, 2, v___x_3464_);
    return v___x_3467_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__12() -> *mut LeanObject {
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    v___x_3468_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__11_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__11,
    );
    v___x_3469_ = lean_unsigned_to_nat(1022);
    v___x_3470_ = l_Lean_Parser_Tactic_Conv_dsimp___closed__1;
    v___x_3471_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3471_, 0, v___x_3470_);
    lean_ctor_set(v___x_3471_, 1, v___x_3469_);
    lean_ctor_set(v___x_3471_, 2, v___x_3468_);
    return v___x_3471_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimp() -> *mut LeanObject {
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    v___x_3472_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimp___closed__12_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimp___closed__12,
    );
    return v___x_3472_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4() -> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3484_ = l_Lean_Parser_Tactic_optConfig;
    v___x_3485_ = l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__3;
    v___x_3486_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3487_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3487_, 0, v___x_3486_);
    lean_ctor_set(v___x_3487_, 1, v___x_3485_);
    lean_ctor_set(v___x_3487_, 2, v___x_3484_);
    return v___x_3487_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5() -> *mut LeanObject {
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    v___x_3488_ = l_Lean_Parser_Tactic_Conv_simp___closed__8;
    v___x_3489_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__4,
    );
    v___x_3490_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3491_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3491_, 0, v___x_3490_);
    lean_ctor_set(v___x_3491_, 1, v___x_3489_);
    lean_ctor_set(v___x_3491_, 2, v___x_3488_);
    return v___x_3491_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6() -> *mut LeanObject {
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    v___x_3492_ = l_Lean_Parser_Tactic_dsimpArgs;
    v___x_3493_ = l_Lean_Parser_Tactic_Conv_argArg___closed__3;
    v___x_3494_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3494_, 0, v___x_3493_);
    lean_ctor_set(v___x_3494_, 1, v___x_3492_);
    return v___x_3494_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7() -> *mut LeanObject {
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    v___x_3495_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__6,
    );
    v___x_3496_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__5,
    );
    v___x_3497_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_3498_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_3498_, 0, v___x_3497_);
    lean_ctor_set(v___x_3498_, 1, v___x_3496_);
    lean_ctor_set(v___x_3498_, 2, v___x_3495_);
    return v___x_3498_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8() -> *mut LeanObject {
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    v___x_3499_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__7,
    );
    v___x_3500_ = lean_unsigned_to_nat(1022);
    v___x_3501_ = l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__1;
    v___x_3502_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_3502_, 0, v___x_3501_);
    lean_ctor_set(v___x_3502_, 1, v___x_3500_);
    lean_ctor_set(v___x_3502_, 2, v___x_3499_);
    return v___x_3502_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_dsimpTrace() -> *mut LeanObject {
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    v___x_3503_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_dsimpTrace___closed__8,
    );
    return v___x_3503_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1(
    mut v_x_3704_: *mut LeanObject,
    mut v_a_3705_: *mut LeanObject,
    mut v_a_3706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u8 = 0;
    v___x_3707_ = l_Lean_Parser_Tactic_Conv_convRfl___closed__1;
    v___x_3708_ = l_Lean_Syntax_isOfKind(v_x_3704_, v___x_3707_);
    if v___x_3708_ == 0 {
        let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
        v___x_3709_ = lean_box(1);
        v___x_3710_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3710_, 0, v___x_3709_);
        lean_ctor_set(v___x_3710_, 1, v_a_3706_);
        return v___x_3710_;
    } else {
        let mut v_ref_3711_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3712_: u8 = 0;
        let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
        v_ref_3711_ = lean_ctor_get(v_a_3705_, 5);
        v___x_3712_ = 0;
        v___x_3713_ = l_Lean_SourceInfo_fromRef(v_ref_3711_, v___x_3712_);
        v___x_3714_ = l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1;
        v___x_3715_ = l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2;
        lean_inc_n(v___x_3713_, 7);
        v___x_3716_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3716_, 0, v___x_3713_);
        lean_ctor_set(v___x_3716_, 1, v___x_3715_);
        v___x_3717_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3718_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3718_, 0, v___x_3713_);
        lean_ctor_set(v___x_3718_, 1, v___x_3717_);
        v___x_3719_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3720_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3721_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3722_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__7;
        v___x_3723_ = l_Lean_Parser_Tactic_Conv_convRfl___closed__2;
        v___x_3724_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3724_, 0, v___x_3713_);
        lean_ctor_set(v___x_3724_, 1, v___x_3723_);
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
        v___x_3730_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3730_, 0, v___x_3729_);
        lean_ctor_set(v___x_3730_, 1, v_a_3706_);
        return v___x_3730_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___boxed(
    mut v_x_3731_: *mut LeanObject,
    mut v_a_3732_: *mut LeanObject,
    mut v_a_3733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3734_: *mut LeanObject = core::ptr::null_mut();
    v_res_3734_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1(v_x_3731_, v_a_3732_, v_a_3733_);
    lean_dec_ref(v_a_3732_);
    return v_res_3734_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1(
    mut v_x_3756_: *mut LeanObject,
    mut v_a_3757_: *mut LeanObject,
    mut v_a_3758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    v___x_3759_ = l_Lean_Parser_Tactic_Conv_convDone___closed__1;
    v___x_3760_ = l_Lean_Syntax_isOfKind(v_x_3756_, v___x_3759_);
    if v___x_3760_ == 0 {
        let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
        v___x_3761_ = lean_box(1);
        v___x_3762_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3762_, 0, v___x_3761_);
        lean_ctor_set(v___x_3762_, 1, v_a_3758_);
        return v___x_3762_;
    } else {
        let mut v_ref_3763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3764_: u8 = 0;
        let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
        v_ref_3763_ = lean_ctor_get(v_a_3757_, 5);
        v___x_3764_ = 0;
        v___x_3765_ = l_Lean_SourceInfo_fromRef(v_ref_3763_, v___x_3764_);
        v___x_3766_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_3767_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_3765_, 7);
        v___x_3768_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3768_, 0, v___x_3765_);
        lean_ctor_set(v___x_3768_, 1, v___x_3767_);
        v___x_3769_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3770_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3770_, 0, v___x_3765_);
        lean_ctor_set(v___x_3770_, 1, v___x_3769_);
        v___x_3771_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3772_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3773_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3774_ = l_Lean_Parser_Tactic_Conv_convDone___closed__2;
        v___x_3775_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___closed__0;
        v___x_3776_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3776_, 0, v___x_3765_);
        lean_ctor_set(v___x_3776_, 1, v___x_3774_);
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
        v___x_3782_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3782_, 0, v___x_3781_);
        lean_ctor_set(v___x_3782_, 1, v_a_3758_);
        return v___x_3782_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1___boxed(
    mut v_x_3783_: *mut LeanObject,
    mut v_a_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3786_: *mut LeanObject = core::ptr::null_mut();
    v_res_3786_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convDone__1(v_x_3783_, v_a_3784_, v_a_3785_);
    lean_dec_ref(v_a_3784_);
    return v_res_3786_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1(
    mut v_x_3809_: *mut LeanObject,
    mut v_a_3810_: *mut LeanObject,
    mut v_a_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: u8 = 0;
    v___x_3812_ = l_Lean_Parser_Tactic_Conv_convTrace__state___closed__1;
    v___x_3813_ = l_Lean_Syntax_isOfKind(v_x_3809_, v___x_3812_);
    if v___x_3813_ == 0 {
        let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
        v___x_3814_ = lean_box(1);
        v___x_3815_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3815_, 0, v___x_3814_);
        lean_ctor_set(v___x_3815_, 1, v_a_3811_);
        return v___x_3815_;
    } else {
        let mut v_ref_3816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3817_: u8 = 0;
        let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
        v_ref_3816_ = lean_ctor_get(v_a_3810_, 5);
        v___x_3817_ = 0;
        v___x_3818_ = l_Lean_SourceInfo_fromRef(v_ref_3816_, v___x_3817_);
        v___x_3819_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_3820_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_3818_, 7);
        v___x_3821_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3821_, 0, v___x_3818_);
        lean_ctor_set(v___x_3821_, 1, v___x_3820_);
        v___x_3822_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3823_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3823_, 0, v___x_3818_);
        lean_ctor_set(v___x_3823_, 1, v___x_3822_);
        v___x_3824_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3825_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3826_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3827_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___closed__1;
        v___x_3828_ = l_Lean_Parser_Tactic_Conv_convTrace__state___closed__2;
        v___x_3829_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3829_, 0, v___x_3818_);
        lean_ctor_set(v___x_3829_, 1, v___x_3828_);
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
        v___x_3835_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3835_, 0, v___x_3834_);
        lean_ctor_set(v___x_3835_, 1, v_a_3811_);
        return v___x_3835_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1___boxed(
    mut v_x_3836_: *mut LeanObject,
    mut v_a_3837_: *mut LeanObject,
    mut v_a_3838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3839_: *mut LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTrace__state__1(v_x_3836_, v_a_3837_, v_a_3838_);
    lean_dec_ref(v_a_3837_);
    return v_res_3839_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1(
    mut v_x_3866_: *mut LeanObject,
    mut v_a_3867_: *mut LeanObject,
    mut v_a_3868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: u8 = 0;
    v___x_3869_ = l_Lean_Parser_Tactic_Conv_allGoals___closed__1;
    lean_inc(v_x_3866_);
    v___x_3870_ = l_Lean_Syntax_isOfKind(v_x_3866_, v___x_3869_);
    if v___x_3870_ == 0 {
        let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3866_);
        v___x_3871_ = lean_box(1);
        v___x_3872_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3872_, 0, v___x_3871_);
        lean_ctor_set(v___x_3872_, 1, v_a_3868_);
        return v___x_3872_;
    } else {
        let mut v_ref_3873_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tk_3875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3878_: u8 = 0;
        let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
        v_ref_3873_ = lean_ctor_get(v_a_3867_, 5);
        v___x_3874_ = lean_unsigned_to_nat(0);
        v_tk_3875_ = l_Lean_Syntax_getArg(v_x_3866_, v___x_3874_);
        v___x_3876_ = lean_unsigned_to_nat(1);
        v___x_3877_ = l_Lean_Syntax_getArg(v_x_3866_, v___x_3876_);
        lean_dec(v_x_3866_);
        v___x_3878_ = 0;
        v___x_3879_ = l_Lean_SourceInfo_fromRef(v_ref_3873_, v___x_3878_);
        v___x_3880_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_3881_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_3879_, 11);
        v___x_3882_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3882_, 0, v___x_3879_);
        lean_ctor_set(v___x_3882_, 1, v___x_3881_);
        v___x_3883_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3884_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3884_, 0, v___x_3879_);
        lean_ctor_set(v___x_3884_, 1, v___x_3883_);
        v___x_3885_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3886_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3887_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3888_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__0;
        v___x_3889_ = l_Lean_SourceInfo_fromRef(v_tk_3875_, v___x_3870_);
        lean_dec(v_tk_3875_);
        v___x_3890_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1;
        v___x_3891_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3891_, 0, v___x_3889_);
        lean_ctor_set(v___x_3891_, 1, v___x_3890_);
        v___x_3892_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_3893_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_3894_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3894_, 0, v___x_3879_);
        lean_ctor_set(v___x_3894_, 1, v___x_3893_);
        lean_inc_ref(v___x_3884_);
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
        v___x_3904_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3904_, 0, v___x_3903_);
        lean_ctor_set(v___x_3904_, 1, v_a_3868_);
        return v___x_3904_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___boxed(
    mut v_x_3905_: *mut LeanObject,
    mut v_a_3906_: *mut LeanObject,
    mut v_a_3907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3908_: *mut LeanObject = core::ptr::null_mut();
    v_res_3908_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1(v_x_3905_, v_a_3906_, v_a_3907_);
    lean_dec_ref(v_a_3906_);
    return v_res_3908_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1(
    mut v_x_3935_: *mut LeanObject,
    mut v_a_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    v___x_3938_ = l_Lean_Parser_Tactic_Conv_anyGoals___closed__1;
    lean_inc(v_x_3935_);
    v___x_3939_ = l_Lean_Syntax_isOfKind(v_x_3935_, v___x_3938_);
    if v___x_3939_ == 0 {
        let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3935_);
        v___x_3940_ = lean_box(1);
        v___x_3941_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3941_, 0, v___x_3940_);
        lean_ctor_set(v___x_3941_, 1, v_a_3937_);
        return v___x_3941_;
    } else {
        let mut v_ref_3942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tk_3944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3947_: u8 = 0;
        let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
        v_ref_3942_ = lean_ctor_get(v_a_3936_, 5);
        v___x_3943_ = lean_unsigned_to_nat(0);
        v_tk_3944_ = l_Lean_Syntax_getArg(v_x_3935_, v___x_3943_);
        v___x_3945_ = lean_unsigned_to_nat(1);
        v___x_3946_ = l_Lean_Syntax_getArg(v_x_3935_, v___x_3945_);
        lean_dec(v_x_3935_);
        v___x_3947_ = 0;
        v___x_3948_ = l_Lean_SourceInfo_fromRef(v_ref_3942_, v___x_3947_);
        v___x_3949_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_3950_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_3948_, 11);
        v___x_3951_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3951_, 0, v___x_3948_);
        lean_ctor_set(v___x_3951_, 1, v___x_3950_);
        v___x_3952_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_3953_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3953_, 0, v___x_3948_);
        lean_ctor_set(v___x_3953_, 1, v___x_3952_);
        v___x_3954_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_3955_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_3956_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_3957_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__0;
        v___x_3958_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3939_);
        lean_dec(v_tk_3944_);
        v___x_3959_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___closed__1;
        v___x_3960_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3960_, 0, v___x_3958_);
        lean_ctor_set(v___x_3960_, 1, v___x_3959_);
        v___x_3961_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_3962_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_3963_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_3963_, 0, v___x_3948_);
        lean_ctor_set(v___x_3963_, 1, v___x_3962_);
        lean_inc_ref(v___x_3953_);
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
        v___x_3973_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3973_, 0, v___x_3972_);
        lean_ctor_set(v___x_3973_, 1, v_a_3937_);
        return v___x_3973_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1___boxed(
    mut v_x_3974_: *mut LeanObject,
    mut v_a_3975_: *mut LeanObject,
    mut v_a_3976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3977_: *mut LeanObject = core::ptr::null_mut();
    v_res_3977_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__anyGoals__1(v_x_3974_, v_a_3975_, v_a_3976_);
    lean_dec_ref(v_a_3975_);
    return v_res_3977_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__6() -> *mut LeanObject {
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    v___x_3992_ = 0;
    v___x_3993_ = l_Lean_Parser_Tactic_Conv_case___closed__5;
    v___x_3994_ = l_Lean_Parser_Tactic_Conv_case___closed__4;
    v___x_3995_ = l_Lean_Parser_Tactic_caseArg;
    v___x_3996_ = lean_alloc_ctor(11, 3, (1) as u32);
    lean_ctor_set(v___x_3996_, 0, v___x_3995_);
    lean_ctor_set(v___x_3996_, 1, v___x_3994_);
    lean_ctor_set(v___x_3996_, 2, v___x_3993_);
    lean_ctor_set_uint8(
        v___x_3996_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3992_,
    );
    return v___x_3996_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__7() -> *mut LeanObject {
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    v___x_3997_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__6,
    );
    v___x_3998_ = l_Lean_Parser_Tactic_Conv_case___closed__3;
    v___x_3999_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4000_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4000_, 0, v___x_3999_);
    lean_ctor_set(v___x_4000_, 1, v___x_3998_);
    lean_ctor_set(v___x_4000_, 2, v___x_3997_);
    return v___x_4000_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__8() -> *mut LeanObject {
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    v___x_4001_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5;
    v___x_4002_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__7,
    );
    v___x_4003_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4004_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4004_, 0, v___x_4003_);
    lean_ctor_set(v___x_4004_, 1, v___x_4002_);
    lean_ctor_set(v___x_4004_, 2, v___x_4001_);
    return v___x_4004_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__9() -> *mut LeanObject {
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    v___x_4005_ = l_Lean_Parser_Tactic_Conv_convSeq;
    v___x_4006_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__8,
    );
    v___x_4007_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4008_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4008_, 0, v___x_4007_);
    lean_ctor_set(v___x_4008_, 1, v___x_4006_);
    lean_ctor_set(v___x_4008_, 2, v___x_4005_);
    return v___x_4008_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case___closed__10() -> *mut LeanObject {
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    v___x_4009_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__9_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__9,
    );
    v___x_4010_ = lean_unsigned_to_nat(1022);
    v___x_4011_ = l_Lean_Parser_Tactic_Conv_case___closed__1;
    v___x_4012_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4012_, 0, v___x_4011_);
    lean_ctor_set(v___x_4012_, 1, v___x_4010_);
    lean_ctor_set(v___x_4012_, 2, v___x_4009_);
    return v___x_4012_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case() -> *mut LeanObject {
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    v___x_4013_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__10,
    );
    return v___x_4013_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    v___x_4019_ = l_Array_mkArray0(lean_box(0));
    return v___x_4019_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1(
    mut v_x_4021_: *mut LeanObject,
    mut v_a_4022_: *mut LeanObject,
    mut v_a_4023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: u8 = 0;
    v___x_4024_ = l_Lean_Parser_Tactic_Conv_case___closed__0;
    v___x_4025_ = l_Lean_Parser_Tactic_Conv_case___closed__1;
    lean_inc(v_x_4021_);
    v___x_4026_ = l_Lean_Syntax_isOfKind(v_x_4021_, v___x_4025_);
    if v___x_4026_ == 0 {
        let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4021_);
        v___x_4027_ = lean_box(1);
        v___x_4028_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4028_, 0, v___x_4027_);
        lean_ctor_set(v___x_4028_, 1, v_a_4023_);
        return v___x_4028_;
    } else {
        let mut v_ref_4029_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tk_4031_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
        let mut v_arr_4035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4040_: u8 = 0;
        let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4029_ = lean_ctor_get(v_a_4022_, 5);
        v___x_4030_ = lean_unsigned_to_nat(0);
        v_tk_4031_ = l_Lean_Syntax_getArg(v_x_4021_, v___x_4030_);
        v___x_4032_ = lean_unsigned_to_nat(1);
        v___x_4033_ = l_Lean_Syntax_getArg(v_x_4021_, v___x_4032_);
        v___x_4034_ = lean_unsigned_to_nat(2);
        v_arr_4035_ = l_Lean_Syntax_getArg(v_x_4021_, v___x_4034_);
        v___x_4036_ = lean_unsigned_to_nat(3);
        v___x_4037_ = l_Lean_Syntax_getArg(v_x_4021_, v___x_4036_);
        lean_dec(v_x_4021_);
        v___x_4038_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__1;
        v___x_4039_ = l_Lean_Syntax_getArgs(v___x_4033_);
        lean_dec(v___x_4033_);
        v___x_4040_ = 0;
        v___x_4041_ = l_Lean_SourceInfo_fromRef(v_ref_4029_, v___x_4040_);
        v___x_4042_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_4043_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_4041_, 26);
        v___x_4044_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4044_, 0, v___x_4041_);
        lean_ctor_set(v___x_4044_, 1, v___x_4043_);
        v___x_4045_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4046_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4046_, 0, v___x_4041_);
        lean_ctor_set(v___x_4046_, 1, v___x_4045_);
        v___x_4047_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4048_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4049_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4050_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__0;
        v___x_4051_ = l_Lean_SourceInfo_fromRef(v_tk_4031_, v___x_4026_);
        lean_dec(v_tk_4031_);
        v___x_4052_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4052_, 0, v___x_4051_);
        lean_ctor_set(v___x_4052_, 1, v___x_4024_);
        v___x_4053_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4054_ = l_Array_append___redArg(v___x_4053_, v___x_4039_);
        lean_dec_ref(v___x_4039_);
        v___x_4055_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4055_, 0, v___x_4041_);
        lean_ctor_set(v___x_4055_, 1, v___x_4049_);
        lean_ctor_set(v___x_4055_, 2, v___x_4054_);
        v___x_4056_ = l_Lean_SourceInfo_fromRef(v_arr_4035_, v___x_4026_);
        lean_dec(v_arr_4035_);
        v___x_4057_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4057_, 0, v___x_4056_);
        lean_ctor_set(v___x_4057_, 1, v___x_4045_);
        v___x_4058_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_4059_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_4060_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4060_, 0, v___x_4041_);
        lean_ctor_set(v___x_4060_, 1, v___x_4059_);
        v___x_4061_ = l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3;
        v___x_4062_ = l_Lean_Parser_Tactic_Conv_paren___closed__1;
        v___x_4063_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        v___x_4064_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4064_, 0, v___x_4041_);
        lean_ctor_set(v___x_4064_, 1, v___x_4063_);
        v___x_4065_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_4066_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4066_, 0, v___x_4041_);
        lean_ctor_set(v___x_4066_, 1, v___x_4065_);
        v___x_4067_ = l_Lean_Syntax_node3(
            v___x_4041_,
            v___x_4062_,
            v___x_4064_,
            v___x_4037_,
            v___x_4066_,
        );
        v___x_4068_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2;
        v___x_4069_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4069_, 0, v___x_4041_);
        lean_ctor_set(v___x_4069_, 1, v___x_4068_);
        v___x_4070_ = l_Lean_Parser_Tactic_Conv_allGoals___closed__1;
        v___x_4071_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__allGoals__1___closed__1;
        v___x_4072_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4072_, 0, v___x_4041_);
        lean_ctor_set(v___x_4072_, 1, v___x_4071_);
        v___x_4073_ = l_Lean_Parser_Tactic_Conv_convRfl___closed__1;
        v___x_4074_ = l_Lean_Parser_Tactic_Conv_convRfl___closed__2;
        v___x_4075_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4075_, 0, v___x_4041_);
        lean_ctor_set(v___x_4075_, 1, v___x_4074_);
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
        lean_inc_ref(v___x_4046_);
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
        v___x_4093_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4093_, 0, v___x_4092_);
        lean_ctor_set(v___x_4093_, 1, v_a_4023_);
        return v___x_4093_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___boxed(
    mut v_x_4094_: *mut LeanObject,
    mut v_a_4095_: *mut LeanObject,
    mut v_a_4096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4097_: *mut LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1(v_x_4094_, v_a_4095_, v_a_4096_);
    lean_dec_ref(v_a_4095_);
    return v_res_4097_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__4() -> *mut LeanObject {
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    v___x_4109_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_case___closed__6,
    );
    v___x_4110_ = l_Lean_Parser_Tactic_Conv_case_x27___closed__3;
    v___x_4111_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4112_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4112_, 0, v___x_4111_);
    lean_ctor_set(v___x_4112_, 1, v___x_4110_);
    lean_ctor_set(v___x_4112_, 2, v___x_4109_);
    return v___x_4112_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__5() -> *mut LeanObject {
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    v___x_4113_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5;
    v___x_4114_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__4,
    );
    v___x_4115_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4116_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4116_, 0, v___x_4115_);
    lean_ctor_set(v___x_4116_, 1, v___x_4114_);
    lean_ctor_set(v___x_4116_, 2, v___x_4113_);
    return v___x_4116_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__6() -> *mut LeanObject {
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    v___x_4117_ = l_Lean_Parser_Tactic_Conv_convSeq;
    v___x_4118_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__5,
    );
    v___x_4119_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4120_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4120_, 0, v___x_4119_);
    lean_ctor_set(v___x_4120_, 1, v___x_4118_);
    lean_ctor_set(v___x_4120_, 2, v___x_4117_);
    return v___x_4120_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__7() -> *mut LeanObject {
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    v___x_4121_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__6,
    );
    v___x_4122_ = lean_unsigned_to_nat(1022);
    v___x_4123_ = l_Lean_Parser_Tactic_Conv_case_x27___closed__1;
    v___x_4124_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4124_, 0, v___x_4123_);
    lean_ctor_set(v___x_4124_, 1, v___x_4122_);
    lean_ctor_set(v___x_4124_, 2, v___x_4121_);
    return v___x_4124_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_case_x27() -> *mut LeanObject {
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    v___x_4125_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_case_x27___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_case_x27___closed__7,
    );
    return v___x_4125_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1(
    mut v_x_4131_: *mut LeanObject,
    mut v_a_4132_: *mut LeanObject,
    mut v_a_4133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: u8 = 0;
    v___x_4134_ = l_Lean_Parser_Tactic_Conv_case_x27___closed__0;
    v___x_4135_ = l_Lean_Parser_Tactic_Conv_case_x27___closed__1;
    lean_inc(v_x_4131_);
    v___x_4136_ = l_Lean_Syntax_isOfKind(v_x_4131_, v___x_4135_);
    if v___x_4136_ == 0 {
        let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4131_);
        v___x_4137_ = lean_box(1);
        v___x_4138_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4138_, 0, v___x_4137_);
        lean_ctor_set(v___x_4138_, 1, v_a_4133_);
        return v___x_4138_;
    } else {
        let mut v_ref_4139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tk_4141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
        let mut v_arr_4145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4149_: u8 = 0;
        let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4139_ = lean_ctor_get(v_a_4132_, 5);
        v___x_4140_ = lean_unsigned_to_nat(0);
        v_tk_4141_ = l_Lean_Syntax_getArg(v_x_4131_, v___x_4140_);
        v___x_4142_ = lean_unsigned_to_nat(1);
        v___x_4143_ = l_Lean_Syntax_getArg(v_x_4131_, v___x_4142_);
        v___x_4144_ = lean_unsigned_to_nat(2);
        v_arr_4145_ = l_Lean_Syntax_getArg(v_x_4131_, v___x_4144_);
        v___x_4146_ = lean_unsigned_to_nat(3);
        v___x_4147_ = l_Lean_Syntax_getArg(v_x_4131_, v___x_4146_);
        lean_dec(v_x_4131_);
        v___x_4148_ = l_Lean_Syntax_getArgs(v___x_4143_);
        lean_dec(v___x_4143_);
        v___x_4149_ = 0;
        v___x_4150_ = l_Lean_SourceInfo_fromRef(v_ref_4139_, v___x_4149_);
        v___x_4151_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_4152_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_4150_, 12);
        v___x_4153_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4153_, 0, v___x_4150_);
        lean_ctor_set(v___x_4153_, 1, v___x_4152_);
        v___x_4154_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4155_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4155_, 0, v___x_4150_);
        lean_ctor_set(v___x_4155_, 1, v___x_4154_);
        v___x_4156_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4157_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4158_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4159_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___closed__0;
        v___x_4160_ = l_Lean_SourceInfo_fromRef(v_tk_4141_, v___x_4136_);
        lean_dec(v_tk_4141_);
        v___x_4161_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4161_, 0, v___x_4160_);
        lean_ctor_set(v___x_4161_, 1, v___x_4134_);
        v___x_4162_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4163_ = l_Array_append___redArg(v___x_4162_, v___x_4148_);
        lean_dec_ref(v___x_4148_);
        v___x_4164_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4164_, 0, v___x_4150_);
        lean_ctor_set(v___x_4164_, 1, v___x_4158_);
        lean_ctor_set(v___x_4164_, 2, v___x_4163_);
        v___x_4165_ = l_Lean_SourceInfo_fromRef(v_arr_4145_, v___x_4136_);
        lean_dec(v_arr_4145_);
        v___x_4166_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4166_, 0, v___x_4165_);
        lean_ctor_set(v___x_4166_, 1, v___x_4154_);
        v___x_4167_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_4168_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_4169_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4169_, 0, v___x_4150_);
        lean_ctor_set(v___x_4169_, 1, v___x_4168_);
        lean_inc_ref(v___x_4155_);
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
        v___x_4179_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4179_, 0, v___x_4178_);
        lean_ctor_set(v___x_4179_, 1, v_a_4133_);
        return v___x_4179_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1___boxed(
    mut v_x_4180_: *mut LeanObject,
    mut v_a_4181_: *mut LeanObject,
    mut v_a_4182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4183_: *mut LeanObject = core::ptr::null_mut();
    v_res_4183_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case_x27__1(v_x_4180_, v_a_4181_, v_a_4182_);
    lean_dec_ref(v_a_4181_);
    return v_res_4183_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4()
-> *mut LeanObject {
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    v___x_4195_ = l_Lean_binderIdent;
    v___x_4196_ = l_Lean_Parser_Tactic_Conv_withAnnotateState___closed__10;
    v___x_4197_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4198_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4198_, 0, v___x_4197_);
    lean_ctor_set(v___x_4198_, 1, v___x_4196_);
    lean_ctor_set(v___x_4198_, 2, v___x_4195_);
    return v___x_4198_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5()
-> *mut LeanObject {
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    v___x_4199_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__4,
    );
    v___x_4200_ = l_Lean_Parser_Tactic_Conv_ext___closed__4;
    v___x_4201_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4201_, 0, v___x_4200_);
    lean_ctor_set(v___x_4201_, 1, v___x_4199_);
    return v___x_4201_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6()
-> *mut LeanObject {
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    v___x_4202_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__5,
    );
    v___x_4203_ = l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__3;
    v___x_4204_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4205_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4205_, 0, v___x_4204_);
    lean_ctor_set(v___x_4205_, 1, v___x_4203_);
    lean_ctor_set(v___x_4205_, 2, v___x_4202_);
    return v___x_4205_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7()
-> *mut LeanObject {
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    v___x_4206_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__5;
    v___x_4207_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__6,
    );
    v___x_4208_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4209_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4209_, 0, v___x_4208_);
    lean_ctor_set(v___x_4209_, 1, v___x_4207_);
    lean_ctor_set(v___x_4209_, 2, v___x_4206_);
    return v___x_4209_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8()
-> *mut LeanObject {
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    v___x_4210_ = l_Lean_Parser_Tactic_Conv_convSeq;
    v___x_4211_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__7,
    );
    v___x_4212_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4213_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4213_, 0, v___x_4212_);
    lean_ctor_set(v___x_4213_, 1, v___x_4211_);
    lean_ctor_set(v___x_4213_, 2, v___x_4210_);
    return v___x_4213_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9()
-> *mut LeanObject {
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    v___x_4214_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__8,
    );
    v___x_4215_ = lean_unsigned_to_nat(1022);
    v___x_4216_ = l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1;
    v___x_4217_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4217_, 0, v___x_4216_);
    lean_ctor_set(v___x_4217_, 1, v___x_4215_);
    lean_ctor_set(v___x_4217_, 2, v___x_4214_);
    return v___x_4217_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__() -> *mut LeanObject {
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    v___x_4218_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9_once
        ),
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__9,
    );
    return v___x_4218_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1(
    mut v_x_4236_: *mut LeanObject,
    mut v_a_4237_: *mut LeanObject,
    mut v_a_4238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: u8 = 0;
    v___x_4239_ = l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e___00__closed__1;
    lean_inc(v_x_4236_);
    v___x_4240_ = l_Lean_Syntax_isOfKind(v_x_4236_, v___x_4239_);
    if v___x_4240_ == 0 {
        let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4236_);
        v___x_4241_ = lean_box(1);
        v___x_4242_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4242_, 0, v___x_4241_);
        lean_ctor_set(v___x_4242_, 1, v_a_4238_);
        return v___x_4242_;
    } else {
        let mut v_ref_4243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
        let mut v_args_4249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4250_: u8 = 0;
        let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4243_ = lean_ctor_get(v_a_4237_, 5);
        v___x_4244_ = lean_unsigned_to_nat(1);
        v___x_4245_ = l_Lean_Syntax_getArg(v_x_4236_, v___x_4244_);
        v___x_4246_ = lean_unsigned_to_nat(3);
        v___x_4247_ = l_Lean_Syntax_getArg(v_x_4236_, v___x_4246_);
        lean_dec(v_x_4236_);
        v___x_4248_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__1;
        v_args_4249_ = l_Lean_Syntax_getArgs(v___x_4245_);
        lean_dec(v___x_4245_);
        v___x_4250_ = 0;
        v___x_4251_ = l_Lean_SourceInfo_fromRef(v_ref_4243_, v___x_4250_);
        v___x_4252_ = l_Lean_Parser_Tactic_Conv_case___closed__0;
        v___x_4253_ = l_Lean_Parser_Tactic_Conv_case___closed__1;
        lean_inc_n(v___x_4251_, 8);
        v___x_4254_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4254_, 0, v___x_4251_);
        lean_ctor_set(v___x_4254_, 1, v___x_4252_);
        v___x_4255_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4256_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__3;
        v___x_4257_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__5;
        v___x_4258_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___closed__6;
        v___x_4259_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4259_, 0, v___x_4251_);
        lean_ctor_set(v___x_4259_, 1, v___x_4258_);
        v___x_4260_ = l_Lean_Syntax_node1(v___x_4251_, v___x_4257_, v___x_4259_);
        v___x_4261_ = l_Lean_Syntax_node1(v___x_4251_, v___x_4248_, v___x_4260_);
        v___x_4262_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4263_ = l_Array_append___redArg(v___x_4262_, v_args_4249_);
        lean_dec_ref(v_args_4249_);
        v___x_4264_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4264_, 0, v___x_4251_);
        lean_ctor_set(v___x_4264_, 1, v___x_4255_);
        lean_ctor_set(v___x_4264_, 2, v___x_4263_);
        v___x_4265_ = l_Lean_Syntax_node2(v___x_4251_, v___x_4256_, v___x_4261_, v___x_4264_);
        v___x_4266_ = l_Lean_Syntax_node1(v___x_4251_, v___x_4255_, v___x_4265_);
        v___x_4267_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4268_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4268_, 0, v___x_4251_);
        lean_ctor_set(v___x_4268_, 1, v___x_4267_);
        v___x_4269_ = l_Lean_Syntax_node4(
            v___x_4251_,
            v___x_4253_,
            v___x_4254_,
            v___x_4266_,
            v___x_4268_,
            v___x_4247_,
        );
        v___x_4270_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4270_, 0, v___x_4269_);
        lean_ctor_set(v___x_4270_, 1, v_a_4238_);
        return v___x_4270_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1___boxed(
    mut v_x_4271_: *mut LeanObject,
    mut v_a_4272_: *mut LeanObject,
    mut v_a_4273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4274_: *mut LeanObject = core::ptr::null_mut();
    v_res_4274_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convNext_____x3d_x3e____1(v_x_4271_, v_a_4272_, v_a_4273_);
    lean_dec_ref(v_a_4272_);
    return v_res_4274_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1(
    mut v_x_4300_: *mut LeanObject,
    mut v_a_4301_: *mut LeanObject,
    mut v_a_4302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: u8 = 0;
    v___x_4303_ = l_Lean_Parser_Tactic_Conv_focus___closed__0;
    v___x_4304_ = l_Lean_Parser_Tactic_Conv_focus___closed__1;
    lean_inc(v_x_4300_);
    v___x_4305_ = l_Lean_Syntax_isOfKind(v_x_4300_, v___x_4304_);
    if v___x_4305_ == 0 {
        let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4300_);
        v___x_4306_ = lean_box(1);
        v___x_4307_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4307_, 0, v___x_4306_);
        lean_ctor_set(v___x_4307_, 1, v_a_4302_);
        return v___x_4307_;
    } else {
        let mut v_ref_4308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tk_4310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4313_: u8 = 0;
        let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4308_ = lean_ctor_get(v_a_4301_, 5);
        v___x_4309_ = lean_unsigned_to_nat(0);
        v_tk_4310_ = l_Lean_Syntax_getArg(v_x_4300_, v___x_4309_);
        v___x_4311_ = lean_unsigned_to_nat(1);
        v___x_4312_ = l_Lean_Syntax_getArg(v_x_4300_, v___x_4311_);
        lean_dec(v_x_4300_);
        v___x_4313_ = 0;
        v___x_4314_ = l_Lean_SourceInfo_fromRef(v_ref_4308_, v___x_4313_);
        v___x_4315_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_4316_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_4314_, 11);
        v___x_4317_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4317_, 0, v___x_4314_);
        lean_ctor_set(v___x_4317_, 1, v___x_4316_);
        v___x_4318_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4319_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4319_, 0, v___x_4314_);
        lean_ctor_set(v___x_4319_, 1, v___x_4318_);
        v___x_4320_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4321_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4322_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4323_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___closed__0;
        v___x_4324_ = l_Lean_SourceInfo_fromRef(v_tk_4310_, v___x_4305_);
        lean_dec(v_tk_4310_);
        v___x_4325_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4325_, 0, v___x_4324_);
        lean_ctor_set(v___x_4325_, 1, v___x_4303_);
        v___x_4326_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_4327_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_4328_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4328_, 0, v___x_4314_);
        lean_ctor_set(v___x_4328_, 1, v___x_4327_);
        lean_inc_ref(v___x_4319_);
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
        v___x_4338_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4338_, 0, v___x_4337_);
        lean_ctor_set(v___x_4338_, 1, v_a_4302_);
        return v___x_4338_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1___boxed(
    mut v_x_4339_: *mut LeanObject,
    mut v_a_4340_: *mut LeanObject,
    mut v_a_4341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4342_: *mut LeanObject = core::ptr::null_mut();
    v_res_4342_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__focus__1(v_x_4339_, v_a_4340_, v_a_4341_);
    lean_dec_ref(v_a_4340_);
    return v_res_4342_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1(
    mut v_x_4388_: *mut LeanObject,
    mut v_a_4389_: *mut LeanObject,
    mut v_a_4390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: u8 = 0;
    v___x_4391_ = l_Lean_Parser_Tactic_Conv_conv_xb7___00__closed__1;
    lean_inc(v_x_4388_);
    v___x_4392_ = l_Lean_Syntax_isOfKind(v_x_4388_, v___x_4391_);
    if v___x_4392_ == 0 {
        let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4388_);
        v___x_4393_ = lean_box(1);
        v___x_4394_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4394_, 0, v___x_4393_);
        lean_ctor_set(v___x_4394_, 1, v_a_4390_);
        return v___x_4394_;
    } else {
        let mut v_ref_4395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4400_: u8 = 0;
        let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4395_ = lean_ctor_get(v_a_4389_, 5);
        v___x_4396_ = lean_unsigned_to_nat(0);
        v___x_4397_ = l_Lean_Syntax_getArg(v_x_4388_, v___x_4396_);
        v___x_4398_ = lean_unsigned_to_nat(1);
        v___x_4399_ = l_Lean_Syntax_getArg(v_x_4388_, v___x_4398_);
        lean_dec(v_x_4388_);
        v___x_4400_ = 0;
        v___x_4401_ = l_Lean_SourceInfo_fromRef(v_ref_4395_, v___x_4400_);
        v___x_4402_ = l_Lean_Parser_Tactic_Conv_nestedConv___closed__1;
        v___x_4403_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__1;
        v___x_4404_ = l_Lean_SourceInfo_fromRef(v___x_4397_, v___x_4392_);
        lean_dec(v___x_4397_);
        v___x_4405_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__2;
        v___x_4406_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4406_, 0, v___x_4404_);
        lean_ctor_set(v___x_4406_, 1, v___x_4405_);
        v___x_4407_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4408_ = l_Lean_Parser_Tactic_Conv_paren___closed__1;
        v___x_4409_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        lean_inc_n(v___x_4401_, 6);
        v___x_4410_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4410_, 0, v___x_4401_);
        lean_ctor_set(v___x_4410_, 1, v___x_4409_);
        v___x_4411_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_4412_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4412_, 0, v___x_4401_);
        lean_ctor_set(v___x_4412_, 1, v___x_4411_);
        v___x_4413_ = l_Lean_Syntax_node3(
            v___x_4401_,
            v___x_4408_,
            v___x_4410_,
            v___x_4399_,
            v___x_4412_,
        );
        v___x_4414_ = l_Lean_Syntax_node1(v___x_4401_, v___x_4407_, v___x_4413_);
        v___x_4415_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__11;
        v___x_4416_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4416_, 0, v___x_4401_);
        lean_ctor_set(v___x_4416_, 1, v___x_4415_);
        v___x_4417_ = l_Lean_Syntax_node3(
            v___x_4401_,
            v___x_4403_,
            v___x_4406_,
            v___x_4414_,
            v___x_4416_,
        );
        v___x_4418_ = l_Lean_Syntax_node1(v___x_4401_, v___x_4402_, v___x_4417_);
        v___x_4419_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4419_, 0, v___x_4418_);
        lean_ctor_set(v___x_4419_, 1, v_a_4390_);
        return v___x_4419_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1___boxed(
    mut v_x_4420_: *mut LeanObject,
    mut v_a_4421_: *mut LeanObject,
    mut v_a_4422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4423_: *mut LeanObject = core::ptr::null_mut();
    v_res_4423_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv_xb7____1(v_x_4420_, v_a_4421_, v_a_4422_);
    lean_dec_ref(v_a_4421_);
    return v_res_4423_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1(
    mut v_x_4450_: *mut LeanObject,
    mut v_a_4451_: *mut LeanObject,
    mut v_a_4452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: u8 = 0;
    v___x_4453_ = l_Lean_Parser_Tactic_Conv_failIfSuccess___closed__1;
    lean_inc(v_x_4450_);
    v___x_4454_ = l_Lean_Syntax_isOfKind(v_x_4450_, v___x_4453_);
    if v___x_4454_ == 0 {
        let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4450_);
        v___x_4455_ = lean_box(1);
        v___x_4456_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4456_, 0, v___x_4455_);
        lean_ctor_set(v___x_4456_, 1, v_a_4452_);
        return v___x_4456_;
    } else {
        let mut v_ref_4457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tk_4459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4462_: u8 = 0;
        let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4457_ = lean_ctor_get(v_a_4451_, 5);
        v___x_4458_ = lean_unsigned_to_nat(0);
        v_tk_4459_ = l_Lean_Syntax_getArg(v_x_4450_, v___x_4458_);
        v___x_4460_ = lean_unsigned_to_nat(1);
        v___x_4461_ = l_Lean_Syntax_getArg(v_x_4450_, v___x_4460_);
        lean_dec(v_x_4450_);
        v___x_4462_ = 0;
        v___x_4463_ = l_Lean_SourceInfo_fromRef(v_ref_4457_, v___x_4462_);
        v___x_4464_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_4465_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_4463_, 11);
        v___x_4466_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4466_, 0, v___x_4463_);
        lean_ctor_set(v___x_4466_, 1, v___x_4465_);
        v___x_4467_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4468_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4468_, 0, v___x_4463_);
        lean_ctor_set(v___x_4468_, 1, v___x_4467_);
        v___x_4469_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4470_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4471_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4472_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__0;
        v___x_4473_ = l_Lean_SourceInfo_fromRef(v_tk_4459_, v___x_4454_);
        lean_dec(v_tk_4459_);
        v___x_4474_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___closed__1;
        v___x_4475_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4475_, 0, v___x_4473_);
        lean_ctor_set(v___x_4475_, 1, v___x_4474_);
        v___x_4476_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_4477_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_4478_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4478_, 0, v___x_4463_);
        lean_ctor_set(v___x_4478_, 1, v___x_4477_);
        lean_inc_ref(v___x_4468_);
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
        v___x_4488_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4488_, 0, v___x_4487_);
        lean_ctor_set(v___x_4488_, 1, v_a_4452_);
        return v___x_4488_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1___boxed(
    mut v_x_4489_: *mut LeanObject,
    mut v_a_4490_: *mut LeanObject,
    mut v_a_4491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4492_: *mut LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__failIfSuccess__1(v_x_4489_, v_a_4490_, v_a_4491_);
    lean_dec_ref(v_a_4490_);
    return v_res_4492_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4() -> *mut LeanObject {
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    v___x_4504_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4505_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__3;
    v___x_4506_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4507_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4507_, 0, v___x_4506_);
    lean_ctor_set(v___x_4507_, 1, v___x_4505_);
    lean_ctor_set(v___x_4507_, 2, v___x_4504_);
    return v___x_4507_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5() -> *mut LeanObject {
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    v___x_4508_ = l_Lean_Parser_Tactic_rwRuleSeq;
    v___x_4509_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__4,
    );
    v___x_4510_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4511_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4511_, 0, v___x_4510_);
    lean_ctor_set(v___x_4511_, 1, v___x_4509_);
    lean_ctor_set(v___x_4511_, 2, v___x_4508_);
    return v___x_4511_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6() -> *mut LeanObject {
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    v___x_4512_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__5,
    );
    v___x_4513_ = lean_unsigned_to_nat(1022);
    v___x_4514_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1;
    v___x_4515_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4515_, 0, v___x_4514_);
    lean_ctor_set(v___x_4515_, 1, v___x_4513_);
    lean_ctor_set(v___x_4515_, 2, v___x_4512_);
    return v___x_4515_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convRw____() -> *mut LeanObject {
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    v___x_4516_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_convRw_____00__closed__6,
    );
    return v___x_4516_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1(
    mut v_x_4517_: *mut LeanObject,
    mut v_a_4518_: *mut LeanObject,
    mut v_a_4519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: u8 = 0;
    v___x_4520_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1;
    lean_inc(v_x_4517_);
    v___x_4521_ = l_Lean_Syntax_isOfKind(v_x_4517_, v___x_4520_);
    if v___x_4521_ == 0 {
        let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4517_);
        v___x_4522_ = lean_box(1);
        v___x_4523_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4523_, 0, v___x_4522_);
        lean_ctor_set(v___x_4523_, 1, v_a_4519_);
        return v___x_4523_;
    } else {
        let mut v_ref_4524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4529_: u8 = 0;
        let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4524_ = lean_ctor_get(v_a_4518_, 5);
        v___x_4525_ = lean_unsigned_to_nat(1);
        v___x_4526_ = l_Lean_Syntax_getArg(v_x_4517_, v___x_4525_);
        v___x_4527_ = lean_unsigned_to_nat(2);
        v___x_4528_ = l_Lean_Syntax_getArg(v_x_4517_, v___x_4527_);
        lean_dec(v_x_4517_);
        v___x_4529_ = 0;
        v___x_4530_ = l_Lean_SourceInfo_fromRef(v_ref_4524_, v___x_4529_);
        v___x_4531_ = l_Lean_Parser_Tactic_Conv_rewrite___closed__0;
        v___x_4532_ = l_Lean_Parser_Tactic_Conv_rewrite___closed__1;
        lean_inc(v___x_4530_);
        v___x_4533_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4533_, 0, v___x_4530_);
        lean_ctor_set(v___x_4533_, 1, v___x_4531_);
        v___x_4534_ = l_Lean_Syntax_node3(
            v___x_4530_,
            v___x_4532_,
            v___x_4533_,
            v___x_4526_,
            v___x_4528_,
        );
        v___x_4535_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4535_, 0, v___x_4534_);
        lean_ctor_set(v___x_4535_, 1, v_a_4519_);
        return v___x_4535_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1___boxed(
    mut v_x_4536_: *mut LeanObject,
    mut v_a_4537_: *mut LeanObject,
    mut v_a_4538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4539_: *mut LeanObject = core::ptr::null_mut();
    v_res_4539_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRw______1(v_x_4536_, v_a_4537_, v_a_4538_);
    lean_dec_ref(v_a_4537_);
    return v_res_4539_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4() -> *mut LeanObject {
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    v___x_4551_ = l_Lean_Parser_Tactic_optConfig;
    v___x_4552_ = l_Lean_Parser_Tactic_Conv_convErw_____00__closed__3;
    v___x_4553_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4554_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4554_, 0, v___x_4553_);
    lean_ctor_set(v___x_4554_, 1, v___x_4552_);
    lean_ctor_set(v___x_4554_, 2, v___x_4551_);
    return v___x_4554_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5() -> *mut LeanObject {
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    v___x_4555_ = l_Lean_Parser_Tactic_rwRuleSeq;
    v___x_4556_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__4,
    );
    v___x_4557_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4558_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4558_, 0, v___x_4557_);
    lean_ctor_set(v___x_4558_, 1, v___x_4556_);
    lean_ctor_set(v___x_4558_, 2, v___x_4555_);
    return v___x_4558_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6() -> *mut LeanObject {
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    v___x_4559_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__5,
    );
    v___x_4560_ = lean_unsigned_to_nat(1022);
    v___x_4561_ = l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1;
    v___x_4562_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4562_, 0, v___x_4561_);
    lean_ctor_set(v___x_4562_, 1, v___x_4560_);
    lean_ctor_set(v___x_4562_, 2, v___x_4559_);
    return v___x_4562_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convErw____() -> *mut LeanObject {
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    v___x_4563_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_convErw_____00__closed__6,
    );
    return v___x_4563_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(
    mut v_sz_4564_: usize,
    mut v_i_4565_: usize,
    mut v_bs_4566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4567_: u8 = 0;
    let mut v_v_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: usize = 0;
    let mut v___x_4572_: usize = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4567_ = lean_usize_dec_lt(v_i_4565_, v_sz_4564_);
                if v___x_4567_ == 0 {
                    return v_bs_4566_;
                } else {
                    v_v_4568_ = lean_array_uget(v_bs_4566_, v_i_4565_);
                    v___x_4569_ = lean_unsigned_to_nat(0);
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
    mut v_sz_4575_: *mut LeanObject,
    mut v_i_4576_: *mut LeanObject,
    mut v_bs_4577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4578_: usize = 0;
    let mut v_i_boxed_4579_: usize = 0;
    let mut v_res_4580_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4578_ = lean_unbox_usize(v_sz_4575_);
    lean_dec(v_sz_4575_);
    v_i_boxed_4579_ = lean_unbox_usize(v_i_4576_);
    lean_dec(v_i_4576_);
    v_res_4580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(v_sz_boxed_4578_, v_i_boxed_4579_, v_bs_4577_);
    return v_res_4580_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7()
-> *mut LeanObject {
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    v___x_4600_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__6;
    v___x_4601_ = l_String_toRawSubstring_x27(v___x_4600_);
    return v___x_4601_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14()
-> *mut LeanObject {
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    v___x_4613_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__13;
    v___x_4614_ = l_String_toRawSubstring_x27(v___x_4613_);
    return v___x_4614_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1(
    mut v_x_4632_: *mut LeanObject,
    mut v_a_4633_: *mut LeanObject,
    mut v_a_4634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    v___x_4635_ = l_Lean_Parser_Tactic_Conv_convErw_____00__closed__1;
    lean_inc(v_x_4632_);
    v___x_4636_ = l_Lean_Syntax_isOfKind(v_x_4632_, v___x_4635_);
    if v___x_4636_ == 0 {
        let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4632_);
        v___x_4637_ = lean_box(1);
        v___x_4638_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4638_, 0, v___x_4637_);
        lean_ctor_set(v___x_4638_, 1, v_a_4634_);
        return v___x_4638_;
    } else {
        let mut v_quotContext_4639_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_4640_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_4641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4647_: u8 = 0;
        let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4655_: usize = 0;
        let mut v___x_4656_: usize = 0;
        let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_4639_ = lean_ctor_get(v_a_4633_, 1);
        v_currMacroScope_4640_ = lean_ctor_get(v_a_4633_, 2);
        v_ref_4641_ = lean_ctor_get(v_a_4633_, 5);
        v___x_4642_ = lean_unsigned_to_nat(1);
        v___x_4643_ = l_Lean_Syntax_getArg(v_x_4632_, v___x_4642_);
        v___x_4644_ = lean_unsigned_to_nat(2);
        v___x_4645_ = l_Lean_Syntax_getArg(v_x_4632_, v___x_4644_);
        lean_dec(v_x_4632_);
        v___x_4646_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__1;
        v___x_4647_ = 0;
        v___x_4648_ = l_Lean_SourceInfo_fromRef(v_ref_4641_, v___x_4647_);
        v___x_4649_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__1;
        v___x_4650_ = l_Lean_Parser_Tactic_Conv_convRw_____00__closed__2;
        lean_inc_n(v___x_4648_, 12);
        v___x_4651_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4651_, 0, v___x_4648_);
        lean_ctor_set(v___x_4651_, 1, v___x_4650_);
        v___x_4652_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4653_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4654_ = l_Lean_Parser_Tactic_getConfigItems(v___x_4643_);
        v_sz_4655_ = lean_array_size(v___x_4654_);
        v___x_4656_ = 0usize;
        v___x_4657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1_spec__0(v_sz_4655_, v___x_4656_, v___x_4654_);
        v___x_4658_ = l_Array_append___redArg(v___x_4653_, v___x_4657_);
        lean_dec_ref(v___x_4657_);
        v___x_4659_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__3;
        v___x_4660_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__5;
        v___x_4661_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        v___x_4662_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4662_, 0, v___x_4648_);
        lean_ctor_set(v___x_4662_, 1, v___x_4661_);
        v___x_4663_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__7);
        v___x_4664_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__8;
        lean_inc_n(v_currMacroScope_4640_, 2);
        lean_inc_n(v_quotContext_4639_, 2);
        v___x_4665_ =
            l_Lean_addMacroScope(v_quotContext_4639_, v___x_4664_, v_currMacroScope_4640_);
        v___x_4666_ = lean_box(0);
        v___x_4667_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4667_, 0, v___x_4648_);
        lean_ctor_set(v___x_4667_, 1, v___x_4663_);
        lean_ctor_set(v___x_4667_, 2, v___x_4665_);
        lean_ctor_set(v___x_4667_, 3, v___x_4666_);
        v___x_4668_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__9;
        v___x_4669_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4669_, 0, v___x_4648_);
        lean_ctor_set(v___x_4669_, 1, v___x_4668_);
        v___x_4670_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__11;
        v___x_4671_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__12;
        v___x_4672_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4672_, 0, v___x_4648_);
        lean_ctor_set(v___x_4672_, 1, v___x_4671_);
        v___x_4673_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__14);
        v___x_4674_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__15;
        v___x_4675_ =
            l_Lean_addMacroScope(v_quotContext_4639_, v___x_4674_, v_currMacroScope_4640_);
        v___x_4676_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___closed__21;
        v___x_4677_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_4677_, 0, v___x_4648_);
        lean_ctor_set(v___x_4677_, 1, v___x_4673_);
        lean_ctor_set(v___x_4677_, 2, v___x_4675_);
        lean_ctor_set(v___x_4677_, 3, v___x_4676_);
        v___x_4678_ = l_Lean_Syntax_node2(v___x_4648_, v___x_4670_, v___x_4672_, v___x_4677_);
        v___x_4679_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_4680_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4680_, 0, v___x_4648_);
        lean_ctor_set(v___x_4680_, 1, v___x_4679_);
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
        v___x_4684_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4684_, 0, v___x_4648_);
        lean_ctor_set(v___x_4684_, 1, v___x_4652_);
        lean_ctor_set(v___x_4684_, 2, v___x_4683_);
        v___x_4685_ = l_Lean_Syntax_node1(v___x_4648_, v___x_4646_, v___x_4684_);
        v___x_4686_ = l_Lean_Syntax_node3(
            v___x_4648_,
            v___x_4649_,
            v___x_4651_,
            v___x_4685_,
            v___x_4645_,
        );
        v___x_4687_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4687_, 0, v___x_4686_);
        lean_ctor_set(v___x_4687_, 1, v_a_4634_);
        return v___x_4687_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1___boxed(
    mut v_x_4688_: *mut LeanObject,
    mut v_a_4689_: *mut LeanObject,
    mut v_a_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4691_: *mut LeanObject = core::ptr::null_mut();
    v_res_4691_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convErw______1(v_x_4688_, v_a_4689_, v_a_4690_);
    lean_dec_ref(v_a_4689_);
    return v_res_4691_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1(
    mut v_x_4708_: *mut LeanObject,
    mut v_a_4709_: *mut LeanObject,
    mut v_a_4710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: u8 = 0;
    v___x_4711_ = l_Lean_Parser_Tactic_Conv_convArgs___closed__1;
    v___x_4712_ = l_Lean_Syntax_isOfKind(v_x_4708_, v___x_4711_);
    if v___x_4712_ == 0 {
        let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
        v___x_4713_ = lean_box(1);
        v___x_4714_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4714_, 0, v___x_4713_);
        lean_ctor_set(v___x_4714_, 1, v_a_4710_);
        return v___x_4714_;
    } else {
        let mut v_ref_4715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4716_: u8 = 0;
        let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4715_ = lean_ctor_get(v_a_4709_, 5);
        v___x_4716_ = 0;
        v___x_4717_ = l_Lean_SourceInfo_fromRef(v_ref_4715_, v___x_4716_);
        v___x_4718_ = l_Lean_Parser_Tactic_Conv_congr___closed__0;
        v___x_4719_ = l_Lean_Parser_Tactic_Conv_congr___closed__1;
        lean_inc(v___x_4717_);
        v___x_4720_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4720_, 0, v___x_4717_);
        lean_ctor_set(v___x_4720_, 1, v___x_4718_);
        v___x_4721_ = l_Lean_Syntax_node1(v___x_4717_, v___x_4719_, v___x_4720_);
        v___x_4722_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4722_, 0, v___x_4721_);
        lean_ctor_set(v___x_4722_, 1, v_a_4710_);
        return v___x_4722_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1___boxed(
    mut v_x_4723_: *mut LeanObject,
    mut v_a_4724_: *mut LeanObject,
    mut v_a_4725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4726_: *mut LeanObject = core::ptr::null_mut();
    v_res_4726_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convArgs__1(v_x_4723_, v_a_4724_, v_a_4725_);
    lean_dec_ref(v_a_4724_);
    return v_res_4726_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1(
    mut v_x_4743_: *mut LeanObject,
    mut v_a_4744_: *mut LeanObject,
    mut v_a_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: u8 = 0;
    v___x_4746_ = l_Lean_Parser_Tactic_Conv_convLeft___closed__1;
    v___x_4747_ = l_Lean_Syntax_isOfKind(v_x_4743_, v___x_4746_);
    if v___x_4747_ == 0 {
        let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
        v___x_4748_ = lean_box(1);
        v___x_4749_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4749_, 0, v___x_4748_);
        lean_ctor_set(v___x_4749_, 1, v_a_4745_);
        return v___x_4749_;
    } else {
        let mut v_ref_4750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4751_: u8 = 0;
        let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4750_ = lean_ctor_get(v_a_4744_, 5);
        v___x_4751_ = 0;
        v___x_4752_ = l_Lean_SourceInfo_fromRef(v_ref_4750_, v___x_4751_);
        v___x_4753_ = l_Lean_Parser_Tactic_Conv_lhs___closed__0;
        v___x_4754_ = l_Lean_Parser_Tactic_Conv_lhs___closed__1;
        lean_inc(v___x_4752_);
        v___x_4755_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4755_, 0, v___x_4752_);
        lean_ctor_set(v___x_4755_, 1, v___x_4753_);
        v___x_4756_ = l_Lean_Syntax_node1(v___x_4752_, v___x_4754_, v___x_4755_);
        v___x_4757_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4757_, 0, v___x_4756_);
        lean_ctor_set(v___x_4757_, 1, v_a_4745_);
        return v___x_4757_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1___boxed(
    mut v_x_4758_: *mut LeanObject,
    mut v_a_4759_: *mut LeanObject,
    mut v_a_4760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4761_: *mut LeanObject = core::ptr::null_mut();
    v_res_4761_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convLeft__1(v_x_4758_, v_a_4759_, v_a_4760_);
    lean_dec_ref(v_a_4759_);
    return v_res_4761_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1(
    mut v_x_4778_: *mut LeanObject,
    mut v_a_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: u8 = 0;
    v___x_4781_ = l_Lean_Parser_Tactic_Conv_convRight___closed__1;
    v___x_4782_ = l_Lean_Syntax_isOfKind(v_x_4778_, v___x_4781_);
    if v___x_4782_ == 0 {
        let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
        v___x_4783_ = lean_box(1);
        v___x_4784_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4784_, 0, v___x_4783_);
        lean_ctor_set(v___x_4784_, 1, v_a_4780_);
        return v___x_4784_;
    } else {
        let mut v_ref_4785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4786_: u8 = 0;
        let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4785_ = lean_ctor_get(v_a_4779_, 5);
        v___x_4786_ = 0;
        v___x_4787_ = l_Lean_SourceInfo_fromRef(v_ref_4785_, v___x_4786_);
        v___x_4788_ = l_Lean_Parser_Tactic_Conv_rhs___closed__0;
        v___x_4789_ = l_Lean_Parser_Tactic_Conv_rhs___closed__1;
        lean_inc(v___x_4787_);
        v___x_4790_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4790_, 0, v___x_4787_);
        lean_ctor_set(v___x_4790_, 1, v___x_4788_);
        v___x_4791_ = l_Lean_Syntax_node1(v___x_4787_, v___x_4789_, v___x_4790_);
        v___x_4792_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4792_, 0, v___x_4791_);
        lean_ctor_set(v___x_4792_, 1, v_a_4780_);
        return v___x_4792_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1___boxed(
    mut v_x_4793_: *mut LeanObject,
    mut v_a_4794_: *mut LeanObject,
    mut v_a_4795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4796_: *mut LeanObject = core::ptr::null_mut();
    v_res_4796_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRight__1(v_x_4793_, v_a_4794_, v_a_4795_);
    lean_dec_ref(v_a_4794_);
    return v_res_4796_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4() -> *mut LeanObject {
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    v___x_4808_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_ext___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_ext___closed__10,
    );
    v___x_4809_ = l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__3;
    v___x_4810_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4811_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4811_, 0, v___x_4810_);
    lean_ctor_set(v___x_4811_, 1, v___x_4809_);
    lean_ctor_set(v___x_4811_, 2, v___x_4808_);
    return v___x_4811_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5() -> *mut LeanObject {
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    v___x_4812_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__4,
    );
    v___x_4813_ = lean_unsigned_to_nat(1022);
    v___x_4814_ = l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1;
    v___x_4815_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4815_, 0, v___x_4814_);
    lean_ctor_set(v___x_4815_, 1, v___x_4813_);
    lean_ctor_set(v___x_4815_, 2, v___x_4812_);
    return v___x_4815_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_convIntro______() -> *mut LeanObject {
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    v___x_4816_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__5,
    );
    return v___x_4816_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1(
    mut v_x_4817_: *mut LeanObject,
    mut v_a_4818_: *mut LeanObject,
    mut v_a_4819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: u8 = 0;
    v___x_4820_ = l_Lean_Parser_Tactic_Conv_convIntro_______00__closed__1;
    lean_inc(v_x_4817_);
    v___x_4821_ = l_Lean_Syntax_isOfKind(v_x_4817_, v___x_4820_);
    if v___x_4821_ == 0 {
        let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4817_);
        v___x_4822_ = lean_box(1);
        v___x_4823_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4823_, 0, v___x_4822_);
        lean_ctor_set(v___x_4823_, 1, v_a_4819_);
        return v___x_4823_;
    } else {
        let mut v_ref_4824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_4827_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4828_: u8 = 0;
        let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4824_ = lean_ctor_get(v_a_4818_, 5);
        v___x_4825_ = lean_unsigned_to_nat(1);
        v___x_4826_ = l_Lean_Syntax_getArg(v_x_4817_, v___x_4825_);
        lean_dec(v_x_4817_);
        v_xs_4827_ = l_Lean_Syntax_getArgs(v___x_4826_);
        lean_dec(v___x_4826_);
        v___x_4828_ = 0;
        v___x_4829_ = l_Lean_SourceInfo_fromRef(v_ref_4824_, v___x_4828_);
        v___x_4830_ = l_Lean_Parser_Tactic_Conv_ext___closed__0;
        v___x_4831_ = l_Lean_Parser_Tactic_Conv_ext___closed__1;
        lean_inc_n(v___x_4829_, 2);
        v___x_4832_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4832_, 0, v___x_4829_);
        lean_ctor_set(v___x_4832_, 1, v___x_4830_);
        v___x_4833_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4834_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1_once), _init_l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__1);
        v___x_4835_ = l_Array_append___redArg(v___x_4834_, v_xs_4827_);
        lean_dec_ref(v_xs_4827_);
        v___x_4836_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_4836_, 0, v___x_4829_);
        lean_ctor_set(v___x_4836_, 1, v___x_4833_);
        lean_ctor_set(v___x_4836_, 2, v___x_4835_);
        v___x_4837_ = l_Lean_Syntax_node2(v___x_4829_, v___x_4831_, v___x_4832_, v___x_4836_);
        v___x_4838_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4838_, 0, v___x_4837_);
        lean_ctor_set(v___x_4838_, 1, v_a_4819_);
        return v___x_4838_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1___boxed(
    mut v_x_4839_: *mut LeanObject,
    mut v_a_4840_: *mut LeanObject,
    mut v_a_4841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4842_: *mut LeanObject = core::ptr::null_mut();
    v_res_4842_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convIntro________1(v_x_4839_, v_a_4840_, v_a_4841_);
    lean_dec_ref(v_a_4840_);
    return v_res_4842_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__3() -> *mut LeanObject {
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    v___x_4877_ = l_Lean_Parser_Tactic_Conv_enterArg___closed__2;
    v___x_4878_ = l_Lean_binderIdent;
    v___x_4879_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__3;
    v___x_4880_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4880_, 0, v___x_4879_);
    lean_ctor_set(v___x_4880_, 1, v___x_4878_);
    lean_ctor_set(v___x_4880_, 2, v___x_4877_);
    return v___x_4880_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__4() -> *mut LeanObject {
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    v___x_4881_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enterArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enterArg___closed__3_once),
        _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__3,
    );
    v___x_4882_ = l_Lean_Parser_Tactic_Conv_enterArg___closed__1;
    v___x_4883_ = l_Lean_Parser_Tactic_Conv_enterArg___closed__0;
    v___x_4884_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_4884_, 0, v___x_4883_);
    lean_ctor_set(v___x_4884_, 1, v___x_4882_);
    lean_ctor_set(v___x_4884_, 2, v___x_4881_);
    return v___x_4884_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enterArg() -> *mut LeanObject {
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    v___x_4885_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enterArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enterArg___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_enterArg___closed__4,
    );
    return v___x_4885_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__4() -> *mut LeanObject {
    let mut v___x_4900_: u8 = 0;
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    v___x_4900_ = 0;
    v___x_4901_ = l_Lean_Parser_Tactic_Conv_simp___closed__16;
    v___x_4902_ = l_Lean_Parser_Tactic_Conv_simp___closed__14;
    v___x_4903_ = l_Lean_Parser_Tactic_Conv_enterArg;
    v___x_4904_ = lean_alloc_ctor(11, 3, (1) as u32);
    lean_ctor_set(v___x_4904_, 0, v___x_4903_);
    lean_ctor_set(v___x_4904_, 1, v___x_4902_);
    lean_ctor_set(v___x_4904_, 2, v___x_4901_);
    lean_ctor_set_uint8(
        v___x_4904_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4900_,
    );
    return v___x_4904_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__5() -> *mut LeanObject {
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    v___x_4905_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__4,
    );
    v___x_4906_ = l_Lean_Parser_Tactic_Conv_convSeqBracketed___closed__5;
    v___x_4907_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4907_, 0, v___x_4906_);
    lean_ctor_set(v___x_4907_, 1, v___x_4905_);
    return v___x_4907_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__6() -> *mut LeanObject {
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    v___x_4908_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__5,
    );
    v___x_4909_ = l_Lean_Parser_Tactic_Conv_enter___closed__3;
    v___x_4910_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4911_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4911_, 0, v___x_4910_);
    lean_ctor_set(v___x_4911_, 1, v___x_4909_);
    lean_ctor_set(v___x_4911_, 2, v___x_4908_);
    return v___x_4911_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__7() -> *mut LeanObject {
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    v___x_4912_ = l_Lean_Parser_Tactic_Conv_simp___closed__21;
    v___x_4913_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__6_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__6,
    );
    v___x_4914_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_4915_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_4915_, 0, v___x_4914_);
    lean_ctor_set(v___x_4915_, 1, v___x_4913_);
    lean_ctor_set(v___x_4915_, 2, v___x_4912_);
    return v___x_4915_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter___closed__8() -> *mut LeanObject {
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    v___x_4916_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__7_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__7,
    );
    v___x_4917_ = lean_unsigned_to_nat(1024);
    v___x_4918_ = l_Lean_Parser_Tactic_Conv_enter___closed__1;
    v___x_4919_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_4919_, 0, v___x_4918_);
    lean_ctor_set(v___x_4919_, 1, v___x_4917_);
    lean_ctor_set(v___x_4919_, 2, v___x_4916_);
    return v___x_4919_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_enter() -> *mut LeanObject {
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    v___x_4920_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_enter___closed__8_once),
        _init_l_Lean_Parser_Tactic_Conv_enter___closed__8,
    );
    return v___x_4920_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1(
    mut v_x_4947_: *mut LeanObject,
    mut v_a_4948_: *mut LeanObject,
    mut v_a_4949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: u8 = 0;
    v___x_4950_ = l_Lean_Parser_Tactic_Conv_convApply___00__closed__1;
    lean_inc(v_x_4947_);
    v___x_4951_ = l_Lean_Syntax_isOfKind(v_x_4947_, v___x_4950_);
    if v___x_4951_ == 0 {
        let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4947_);
        v___x_4952_ = lean_box(1);
        v___x_4953_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4953_, 0, v___x_4952_);
        lean_ctor_set(v___x_4953_, 1, v_a_4949_);
        return v___x_4953_;
    } else {
        let mut v_ref_4954_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4957_: u8 = 0;
        let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
        v_ref_4954_ = lean_ctor_get(v_a_4948_, 5);
        v___x_4955_ = lean_unsigned_to_nat(1);
        v___x_4956_ = l_Lean_Syntax_getArg(v_x_4947_, v___x_4955_);
        lean_dec(v_x_4947_);
        v___x_4957_ = 0;
        v___x_4958_ = l_Lean_SourceInfo_fromRef(v_ref_4954_, v___x_4957_);
        v___x_4959_ = l_Lean_Parser_Tactic_Conv_nestedTactic___closed__1;
        v___x_4960_ = l_Lean_Parser_Tactic_Conv_nestedTactic___closed__2;
        lean_inc_n(v___x_4958_, 7);
        v___x_4961_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4961_, 0, v___x_4958_);
        lean_ctor_set(v___x_4961_, 1, v___x_4960_);
        v___x_4962_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_4963_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4963_, 0, v___x_4958_);
        lean_ctor_set(v___x_4963_, 1, v___x_4962_);
        v___x_4964_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_4965_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_4966_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_4967_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__0;
        v___x_4968_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___closed__1;
        v___x_4969_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_4969_, 0, v___x_4958_);
        lean_ctor_set(v___x_4969_, 1, v___x_4967_);
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
        v___x_4975_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4975_, 0, v___x_4974_);
        lean_ctor_set(v___x_4975_, 1, v_a_4949_);
        return v___x_4975_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1___boxed(
    mut v_x_4976_: *mut LeanObject,
    mut v_a_4977_: *mut LeanObject,
    mut v_a_4978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4979_: *mut LeanObject = core::ptr::null_mut();
    v_res_4979_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convApply____1(v_x_4976_, v_a_4977_, v_a_4978_);
    lean_dec_ref(v_a_4977_);
    return v_res_4979_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1(
    mut v_x_5066_: *mut LeanObject,
    mut v_a_5067_: *mut LeanObject,
    mut v_a_5068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: u8 = 0;
    v___x_5069_ = l_Lean_Parser_Tactic_Conv_convTry___00__closed__1;
    lean_inc(v_x_5066_);
    v___x_5070_ = l_Lean_Syntax_isOfKind(v_x_5066_, v___x_5069_);
    if v___x_5070_ == 0 {
        let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5066_);
        v___x_5071_ = lean_box(1);
        v___x_5072_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5072_, 0, v___x_5071_);
        lean_ctor_set(v___x_5072_, 1, v_a_5068_);
        return v___x_5072_;
    } else {
        let mut v_ref_5073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5077_: u8 = 0;
        let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
        v_ref_5073_ = lean_ctor_get(v_a_5067_, 5);
        v___x_5074_ = lean_unsigned_to_nat(1);
        v___x_5075_ = l_Lean_Syntax_getArg(v_x_5066_, v___x_5074_);
        lean_dec(v_x_5066_);
        v___x_5076_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__1;
        v___x_5077_ = 0;
        v___x_5078_ = l_Lean_SourceInfo_fromRef(v_ref_5073_, v___x_5077_);
        v___x_5079_ = l_Lean_Parser_Tactic_Conv_first___closed__0;
        v___x_5080_ = l_Lean_Parser_Tactic_Conv_first___closed__1;
        lean_inc_n(v___x_5078_, 10);
        v___x_5081_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5081_, 0, v___x_5078_);
        lean_ctor_set(v___x_5081_, 1, v___x_5079_);
        v___x_5082_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_5083_ = l_Lean_Parser_Tactic_Conv_first___closed__7;
        v___x_5084_ = l_Lean_Parser_Tactic_Conv_case___closed__4;
        v___x_5085_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5085_, 0, v___x_5078_);
        lean_ctor_set(v___x_5085_, 1, v___x_5084_);
        lean_inc_ref(v___x_5085_);
        v___x_5086_ = l_Lean_Syntax_node2(v___x_5078_, v___x_5083_, v___x_5085_, v___x_5075_);
        v___x_5087_ = l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3;
        v___x_5088_ = l_Lean_Parser_Tactic_Conv_skip___closed__0;
        v___x_5089_ = l_Lean_Parser_Tactic_Conv_skip___closed__1;
        v___x_5090_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5090_, 0, v___x_5078_);
        lean_ctor_set(v___x_5090_, 1, v___x_5088_);
        v___x_5091_ = l_Lean_Syntax_node1(v___x_5078_, v___x_5089_, v___x_5090_);
        v___x_5092_ = l_Lean_Syntax_node1(v___x_5078_, v___x_5082_, v___x_5091_);
        v___x_5093_ = l_Lean_Syntax_node1(v___x_5078_, v___x_5087_, v___x_5092_);
        v___x_5094_ = l_Lean_Syntax_node1(v___x_5078_, v___x_5076_, v___x_5093_);
        v___x_5095_ = l_Lean_Syntax_node2(v___x_5078_, v___x_5083_, v___x_5085_, v___x_5094_);
        v___x_5096_ = l_Lean_Syntax_node2(v___x_5078_, v___x_5082_, v___x_5086_, v___x_5095_);
        v___x_5097_ = l_Lean_Syntax_node2(v___x_5078_, v___x_5080_, v___x_5081_, v___x_5096_);
        v___x_5098_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5098_, 0, v___x_5097_);
        lean_ctor_set(v___x_5098_, 1, v_a_5068_);
        return v___x_5098_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1___boxed(
    mut v_x_5099_: *mut LeanObject,
    mut v_a_5100_: *mut LeanObject,
    mut v_a_5101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5102_: *mut LeanObject = core::ptr::null_mut();
    v_res_5102_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convTry____1(v_x_5099_, v_a_5100_, v_a_5101_);
    lean_dec_ref(v_a_5100_);
    return v_res_5102_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1(
    mut v_x_5135_: *mut LeanObject,
    mut v_a_5136_: *mut LeanObject,
    mut v_a_5137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: u8 = 0;
    v___x_5138_ = l_Lean_Parser_Tactic_Conv_conv___x3c_x3b_x3e___00__closed__1;
    lean_inc(v_x_5135_);
    v___x_5139_ = l_Lean_Syntax_isOfKind(v_x_5135_, v___x_5138_);
    if v___x_5139_ == 0 {
        let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5135_);
        v___x_5140_ = lean_box(1);
        v___x_5141_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5141_, 0, v___x_5140_);
        lean_ctor_set(v___x_5141_, 1, v_a_5137_);
        return v___x_5141_;
    } else {
        let mut v_ref_5142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tk_5146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5149_: u8 = 0;
        let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
        v_ref_5142_ = lean_ctor_get(v_a_5136_, 5);
        v___x_5143_ = lean_unsigned_to_nat(0);
        v___x_5144_ = l_Lean_Syntax_getArg(v_x_5135_, v___x_5143_);
        v___x_5145_ = lean_unsigned_to_nat(1);
        v_tk_5146_ = l_Lean_Syntax_getArg(v_x_5135_, v___x_5145_);
        v___x_5147_ = lean_unsigned_to_nat(2);
        v___x_5148_ = l_Lean_Syntax_getArg(v_x_5135_, v___x_5147_);
        lean_dec(v_x_5135_);
        v___x_5149_ = 0;
        v___x_5150_ = l_Lean_SourceInfo_fromRef(v_ref_5142_, v___x_5149_);
        v___x_5151_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__1;
        v___x_5152_ = l_Lean_Parser_Tactic_Conv_nestedTacticCore___closed__2;
        lean_inc_n(v___x_5150_, 25);
        v___x_5153_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5153_, 0, v___x_5150_);
        lean_ctor_set(v___x_5153_, 1, v___x_5152_);
        v___x_5154_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__0;
        v___x_5155_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5155_, 0, v___x_5150_);
        lean_ctor_set(v___x_5155_, 1, v___x_5154_);
        v___x_5156_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__1;
        v___x_5157_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__3;
        v___x_5158_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_5159_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__1;
        v___x_5160_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__2;
        v___x_5161_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        v___x_5162_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5162_, 0, v___x_5150_);
        lean_ctor_set(v___x_5162_, 1, v___x_5161_);
        v___x_5163_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__1;
        v___x_5164_ = l_Lean_Parser_Tactic_Conv_convTactic___closed__2;
        v___x_5165_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5165_, 0, v___x_5150_);
        lean_ctor_set(v___x_5165_, 1, v___x_5164_);
        v___x_5166_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__1;
        v___x_5167_ = l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3;
        v___x_5168_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5158_, v___x_5144_);
        v___x_5169_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5167_, v___x_5168_);
        v___x_5170_ = l_Lean_Syntax_node1(v___x_5150_, v___x_5166_, v___x_5169_);
        lean_inc_ref_n(v___x_5155_, 2);
        lean_inc_ref(v___x_5165_);
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
        v___x_5176_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5176_, 0, v___x_5150_);
        lean_ctor_set(v___x_5176_, 1, v___x_5175_);
        lean_inc_ref(v___x_5176_);
        lean_inc_ref(v___x_5162_);
        v___x_5177_ = l_Lean_Syntax_node3(
            v___x_5150_,
            v___x_5160_,
            v___x_5162_,
            v___x_5174_,
            v___x_5176_,
        );
        v___x_5178_ = l_Lean_SourceInfo_fromRef(v_tk_5146_, v___x_5139_);
        lean_dec(v_tk_5146_);
        v___x_5179_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___closed__3;
        v___x_5180_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5180_, 0, v___x_5178_);
        lean_ctor_set(v___x_5180_, 1, v___x_5179_);
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
        v___x_5194_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5194_, 0, v___x_5193_);
        lean_ctor_set(v___x_5194_, 1, v_a_5137_);
        return v___x_5194_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1___boxed(
    mut v_x_5195_: *mut LeanObject,
    mut v_a_5196_: *mut LeanObject,
    mut v_a_5197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5198_: *mut LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__conv___x3c_x3b_x3e____1(v_x_5195_, v_a_5196_, v_a_5197_);
    lean_dec_ref(v_a_5196_);
    return v_res_5198_;
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1(
    mut v_x_5220_: *mut LeanObject,
    mut v_a_5221_: *mut LeanObject,
    mut v_a_5222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: u8 = 0;
    v___x_5223_ = l_Lean_Parser_Tactic_Conv_convRepeat___00__closed__1;
    lean_inc(v_x_5220_);
    v___x_5224_ = l_Lean_Syntax_isOfKind(v_x_5220_, v___x_5223_);
    if v___x_5224_ == 0 {
        let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5220_);
        v___x_5225_ = lean_box(1);
        v___x_5226_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5226_, 0, v___x_5225_);
        lean_ctor_set(v___x_5226_, 1, v_a_5222_);
        return v___x_5226_;
    } else {
        let mut v_ref_5227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5231_: u8 = 0;
        let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
        v_ref_5227_ = lean_ctor_get(v_a_5221_, 5);
        v___x_5228_ = lean_unsigned_to_nat(1);
        v___x_5229_ = l_Lean_Syntax_getArg(v_x_5220_, v___x_5228_);
        lean_dec(v_x_5220_);
        v___x_5230_ = l_Lean_Parser_Tactic_Conv_convSeq___closed__1;
        v___x_5231_ = 0;
        v___x_5232_ = l_Lean_SourceInfo_fromRef(v_ref_5227_, v___x_5231_);
        v___x_5233_ = l_Lean_Parser_Tactic_Conv_first___closed__0;
        v___x_5234_ = l_Lean_Parser_Tactic_Conv_first___closed__1;
        lean_inc_n(v___x_5232_, 19);
        v___x_5235_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5235_, 0, v___x_5232_);
        lean_ctor_set(v___x_5235_, 1, v___x_5233_);
        v___x_5236_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRfl__1___closed__5;
        v___x_5237_ = l_Lean_Parser_Tactic_Conv_first___closed__7;
        v___x_5238_ = l_Lean_Parser_Tactic_Conv_case___closed__4;
        v___x_5239_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5239_, 0, v___x_5232_);
        lean_ctor_set(v___x_5239_, 1, v___x_5238_);
        v___x_5240_ = l_Lean_Parser_Tactic_Conv_convSeq1Indented___closed__3;
        v___x_5241_ = l_Lean_Parser_Tactic_Conv_paren___closed__1;
        v___x_5242_ = l_Lean_Parser_Tactic_Conv_occs___closed__4;
        v___x_5243_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5243_, 0, v___x_5232_);
        lean_ctor_set(v___x_5243_, 1, v___x_5242_);
        v___x_5244_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__13;
        v___x_5245_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5245_, 0, v___x_5232_);
        lean_ctor_set(v___x_5245_, 1, v___x_5244_);
        lean_inc(v___x_5229_);
        v___x_5246_ = l_Lean_Syntax_node3(
            v___x_5232_,
            v___x_5241_,
            v___x_5243_,
            v___x_5229_,
            v___x_5245_,
        );
        v___x_5247_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__case__1___closed__2;
        v___x_5248_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5248_, 0, v___x_5232_);
        lean_ctor_set(v___x_5248_, 1, v___x_5247_);
        v___x_5249_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___closed__0;
        v___x_5250_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5250_, 0, v___x_5232_);
        lean_ctor_set(v___x_5250_, 1, v___x_5249_);
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
        lean_inc_ref(v___x_5239_);
        v___x_5255_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5237_, v___x_5239_, v___x_5254_);
        v___x_5256_ = l_Lean_Parser_Tactic_Conv_skip___closed__0;
        v___x_5257_ = l_Lean_Parser_Tactic_Conv_skip___closed__1;
        v___x_5258_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_5258_, 0, v___x_5232_);
        lean_ctor_set(v___x_5258_, 1, v___x_5256_);
        v___x_5259_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5257_, v___x_5258_);
        v___x_5260_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5236_, v___x_5259_);
        v___x_5261_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5240_, v___x_5260_);
        v___x_5262_ = l_Lean_Syntax_node1(v___x_5232_, v___x_5230_, v___x_5261_);
        v___x_5263_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5237_, v___x_5239_, v___x_5262_);
        v___x_5264_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5236_, v___x_5255_, v___x_5263_);
        v___x_5265_ = l_Lean_Syntax_node2(v___x_5232_, v___x_5234_, v___x_5235_, v___x_5264_);
        v___x_5266_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5266_, 0, v___x_5265_);
        lean_ctor_set(v___x_5266_, 1, v_a_5222_);
        return v___x_5266_;
    }
}
pub unsafe fn l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1___boxed(
    mut v_x_5267_: *mut LeanObject,
    mut v_a_5268_: *mut LeanObject,
    mut v_a_5269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5270_: *mut LeanObject = core::ptr::null_mut();
    v_res_5270_ = l_Lean_Parser_Tactic_Conv___aux__Init__Conv______macroRules__Lean__Parser__Tactic__Conv__convRepeat____1(v_x_5267_, v_a_5268_, v_a_5269_);
    lean_dec_ref(v_a_5268_);
    return v_res_5270_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__4() -> *mut LeanObject {
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    v___x_5282_ = l_Lean_Parser_Tactic_optConfig;
    v___x_5283_ = l_Lean_Parser_Tactic_Conv_extractLets___closed__3;
    v___x_5284_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_5285_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_5285_, 0, v___x_5284_);
    lean_ctor_set(v___x_5285_, 1, v___x_5283_);
    lean_ctor_set(v___x_5285_, 2, v___x_5282_);
    return v___x_5285_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__10() -> *mut LeanObject {
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    v___x_5301_ = l_Lean_Parser_Tactic_Conv_extractLets___closed__9;
    v___x_5302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__4,
    );
    v___x_5303_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_5304_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_5304_, 0, v___x_5303_);
    lean_ctor_set(v___x_5304_, 1, v___x_5302_);
    lean_ctor_set(v___x_5304_, 2, v___x_5301_);
    return v___x_5304_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__11() -> *mut LeanObject {
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    v___x_5305_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__10_once),
        _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__10,
    );
    v___x_5306_ = lean_unsigned_to_nat(1022);
    v___x_5307_ = l_Lean_Parser_Tactic_Conv_extractLets___closed__1;
    v___x_5308_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_5308_, 0, v___x_5307_);
    lean_ctor_set(v___x_5308_, 1, v___x_5306_);
    lean_ctor_set(v___x_5308_, 2, v___x_5305_);
    return v___x_5308_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_extractLets() -> *mut LeanObject {
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    v___x_5309_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_extractLets___closed__11_once),
        _init_l_Lean_Parser_Tactic_Conv_extractLets___closed__11,
    );
    return v___x_5309_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__4() -> *mut LeanObject {
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    v___x_5321_ = l_Lean_Parser_Tactic_optConfig;
    v___x_5322_ = l_Lean_Parser_Tactic_Conv_liftLets___closed__3;
    v___x_5323_ = l_Lean_Parser_Tactic_Conv_conv_quot___closed__8;
    v___x_5324_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_5324_, 0, v___x_5323_);
    lean_ctor_set(v___x_5324_, 1, v___x_5322_);
    lean_ctor_set(v___x_5324_, 2, v___x_5321_);
    return v___x_5324_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__5() -> *mut LeanObject {
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    v___x_5325_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_liftLets___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_liftLets___closed__4_once),
        _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__4,
    );
    v___x_5326_ = lean_unsigned_to_nat(1022);
    v___x_5327_ = l_Lean_Parser_Tactic_Conv_liftLets___closed__1;
    v___x_5328_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_5328_, 0, v___x_5327_);
    lean_ctor_set(v___x_5328_, 1, v___x_5326_);
    lean_ctor_set(v___x_5328_, 2, v___x_5325_);
    return v___x_5328_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_Conv_liftLets() -> *mut LeanObject {
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    v___x_5329_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_liftLets___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_Conv_liftLets___closed__5_once),
        _init_l_Lean_Parser_Tactic_Conv_liftLets___closed__5,
    );
    return v___x_5329_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Conv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Conv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Category_conv = _init_l_Lean_Parser_Category_conv();
    lean_mark_persistent(l_Lean_Parser_Category_conv);
    l_Lean_Parser_Tactic_Conv_ext = _init_l_Lean_Parser_Tactic_Conv_ext();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_ext);
    l_Lean_Parser_Tactic_Conv_rewrite = _init_l_Lean_Parser_Tactic_Conv_rewrite();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_rewrite);
    l_Lean_Parser_Tactic_Conv_simp = _init_l_Lean_Parser_Tactic_Conv_simp();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_simp);
    l_Lean_Parser_Tactic_Conv_simpTrace = _init_l_Lean_Parser_Tactic_Conv_simpTrace();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_simpTrace);
    l_Lean_Parser_Tactic_Conv_dsimp = _init_l_Lean_Parser_Tactic_Conv_dsimp();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_dsimp);
    l_Lean_Parser_Tactic_Conv_dsimpTrace = _init_l_Lean_Parser_Tactic_Conv_dsimpTrace();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_dsimpTrace);
    l_Lean_Parser_Tactic_Conv_case = _init_l_Lean_Parser_Tactic_Conv_case();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_case);
    l_Lean_Parser_Tactic_Conv_case_x27 = _init_l_Lean_Parser_Tactic_Conv_case_x27();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_case_x27);
    l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__ =
        _init_l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convNext_____x3d_x3e__);
    l_Lean_Parser_Tactic_Conv_convRw____ = _init_l_Lean_Parser_Tactic_Conv_convRw____();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convRw____);
    l_Lean_Parser_Tactic_Conv_convErw____ = _init_l_Lean_Parser_Tactic_Conv_convErw____();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convErw____);
    l_Lean_Parser_Tactic_Conv_convIntro______ = _init_l_Lean_Parser_Tactic_Conv_convIntro______();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_convIntro______);
    l_Lean_Parser_Tactic_Conv_enterArg = _init_l_Lean_Parser_Tactic_Conv_enterArg();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_enterArg);
    l_Lean_Parser_Tactic_Conv_enter = _init_l_Lean_Parser_Tactic_Conv_enter();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_enter);
    l_Lean_Parser_Tactic_Conv_extractLets = _init_l_Lean_Parser_Tactic_Conv_extractLets();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_extractLets);
    l_Lean_Parser_Tactic_Conv_liftLets = _init_l_Lean_Parser_Tactic_Conv_liftLets();
    lean_mark_persistent(l_Lean_Parser_Tactic_Conv_liftLets);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Conv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Conv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Conv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Conv(builtin);
}
