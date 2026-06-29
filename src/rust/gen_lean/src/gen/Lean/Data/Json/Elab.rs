// Lean compiler output
// Module: Lean.Data.Json.Elab
// Imports: Lean.Data.Json.FromToJson Lean.Syntax
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_zip___redArg};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_mkStrLit, l_Lean_TSyntax_getId, l_Lean_mkSepArray,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_throwUnsupported___redArg, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_mkAtom, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::Json::FromToJson::{
    initialize_Lean_Data_Json_FromToJson, runtime_initialize_Lean_Data_Json_FromToJson,
};
use crate::r#gen::Lean::Syntax::{
    initialize_Lean_Syntax, l_Lean_Syntax_getAntiquotTerm, l_Lean_Syntax_isAntiquot,
    runtime_initialize_Lean_Syntax,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
pub static l_Lean_Json_json_quot___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Json_json_quot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Json_json_quot___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__2_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Json_json_quot___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [113, 117, 111, 116, 0],
    };
static mut l_Lean_Json_json_quot___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json_json_quot___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_json_quot___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_json_quot___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_json_quot___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__3_value)
                as *mut crate::leanh::LeanObject,
            5855146430765573009 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [106, 115, 111, 110, 0],
    };
static mut l_Lean_Json_json_quot___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json_json_quot___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__5_value)
                as *mut crate::leanh::LeanObject,
            1496082858672845381 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_json_quot___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8725898423626492863 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__7_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Json_json_quot___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__7_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__9_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [96, 40, 106, 115, 111, 110, 124, 32, 0],
    };
static mut l_Lean_Json_json_quot___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__10_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_json_quot___closed__9_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_json_quot___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__5_value)
                as *mut crate::leanh::LeanObject,
            1496082858672845381 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__12_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__11_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__13_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lean_Json_json_quot___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__14_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_quot___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__4_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_quot___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__18_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_json_quot: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_quot___closed__18_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Category_json: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_jsonNull___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [74, 115, 111, 110, 0],
    };
static mut l_Lean_Json_jsonNull___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonNull___closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [106, 115, 111, 110, 78, 117, 108, 108, 0],
    };
static mut l_Lean_Json_jsonNull___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json_jsonNull___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_jsonNull___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_jsonNull___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__2_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__1_value)
                as *mut crate::leanh::LeanObject,
            6441815625461611653 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonNull___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonNull___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Json_jsonNull___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonNull___closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__3_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonNull___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonNull___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonNull___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_jsonNull: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonTrue___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [106, 115, 111, 110, 84, 114, 117, 101, 0],
    };
static mut l_Lean_Json_jsonTrue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json_jsonTrue___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_jsonTrue___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_jsonTrue___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3939548444196331504 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonTrue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonTrue___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Json_jsonTrue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonTrue___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonTrue___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonTrue___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonTrue___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__4_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_jsonTrue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonFalse___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [106, 115, 111, 110, 70, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Json_jsonFalse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json_jsonFalse___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_jsonFalse___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_jsonFalse___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16741917424498121777 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonFalse___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonFalse___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Json_jsonFalse___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonFalse___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonFalse___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonFalse___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonFalse___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__4_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_jsonFalse: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json___00__closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [106, 115, 111, 110, 95, 0],
    };
static mut l_Lean_Json_json___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json___00__closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json_json___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_json___00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_json___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json___00__closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            2939400120207964464 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json___00__closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json___00__closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Lean_Json_json___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json___00__closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json___00__closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            9232979286016572671 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json___00__closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json___00__closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_json___00__closed__3_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_json___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json___00__closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json___00__closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_json__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json___00__closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [106, 115, 111, 110, 45, 95, 0],
    };
static mut l_Lean_Json_json_x2d___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Json_json_x2d___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_json_x2d___00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_json_x2d___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            1577374928637490903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__2_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lean_Json_json_x2d___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__4_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_Json_json_x2d___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__6_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__7_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_Json_json_x2d___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            6110315075117401315 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__9_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d___00__closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_json_x2d__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d____1___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [106, 115, 111, 110, 45, 95, 95, 49, 0],
    };
static mut l_Lean_Json_json_x2d____1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Json_json_x2d____1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_json_x2d____1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_json_x2d____1___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            825643892587853278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d____1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d____1___closed__2_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 0],
    };
static mut l_Lean_Json_json_x2d____1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d____1___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12926801259741997275 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d____1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d____1___closed__4_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d____1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d____1___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d____1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x2d____1___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x2d____1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_json_x2d____1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x2d____1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [106, 115, 111, 110, 91, 95, 93, 0],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Json_json_x5b___x5d___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_json_x5b___x5d___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_json_x5b___x5d___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7321545924606616616 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__4_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_Json_json_x5b___x5d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__5_value: crate::leanh::LeanStringObject<3> =
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
static mut l_Lean_Json_json_x5b___x5d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__7_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 10,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__6_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__9_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_Json_json_x5b___x5d___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__10_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x5b___x5d___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x5b___x5d___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_json_x5b___x5d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonIdent___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [106, 115, 111, 110, 73, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Json_jsonIdent___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json_jsonIdent___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_jsonIdent___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_jsonIdent___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12587031629607699044 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonIdent___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonIdent___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Json_jsonIdent___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonIdent___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__2_value)
                as *mut crate::leanh::LeanObject,
            393173242845875278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonIdent___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonIdent___closed__4_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Lean_Json_jsonIdent___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonIdent___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__4_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonIdent___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonIdent___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__5_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_jsonIdent___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonIdent___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonIdent___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonIdent___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonIdent___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__8_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_jsonIdent: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonField___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [106, 115, 111, 110, 70, 105, 101, 108, 100, 0],
    };
static mut l_Lean_Json_jsonField___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonField___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json_jsonField___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_jsonField___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_jsonField___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1237635856740116479 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonField___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonField___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonField___closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [58, 32, 0],
    };
static mut l_Lean_Json_jsonField___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonField___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonField___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_jsonField___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_jsonField___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonField___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonField___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonIdent___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonField___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonField___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonField___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonField___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonField___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_jsonField___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_jsonField___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonField___closed__6_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_jsonField: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_jsonField___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [106, 115, 111, 110, 123, 95, 125, 0],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Json_json_x7b___x7d___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_json_x7b___x7d___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_json_x7b___x7d___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17073770184511914758 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [123, 0],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__4_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 10,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_jsonField___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x5b___x5d___closed__6_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__6_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [125, 0],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_json_x7b___x7d___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_json_x7b___x7d___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_json_x7b___x7d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_json_x7b___x7d___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_termJson_x25___00__closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 74, 115, 111, 110, 37, 95, 0],
    };
static mut l_Lean_Json_termJson_x25___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Json_termJson_x25___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Json_termJson_x25___00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value)
                as *mut crate::leanh::LeanObject,
            849327805763387095 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Json_termJson_x25___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            9702538094254971911 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_termJson_x25___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_termJson_x25___00__closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [106, 115, 111, 110, 37, 32, 0],
    };
static mut l_Lean_Json_termJson_x25___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_termJson_x25___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_termJson_x25___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_termJson_x25___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_json_quot___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_termJson_x25___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_termJson_x25___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_termJson_x25___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_termJson_x25__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_termJson_x25___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__3_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 117, 112, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__1_value) as *mut crate::leanh::LeanObject,15644373471618144447 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__3_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__3_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__6_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__8_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value) as *mut crate::leanh::LeanObject,849327805763387095 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [106, 115, 111, 110, 37, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__0_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 116, 111, 74, 115, 111, 110, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 111, 74, 115, 111, 110, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4_value) as *mut crate::leanh::LeanObject,14650589042885292753 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 111, 74, 115, 111, 110, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__6_value) as *mut crate::leanh::LeanObject,13404294370033941819 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__4_value) as *mut crate::leanh::LeanObject,5860066403283595504 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__7_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 74, 115, 111, 110, 46, 97, 114, 114, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__12_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 114, 114, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__12_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value) as *mut crate::leanh::LeanObject,849327805763387095 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__12_value) as *mut crate::leanh::LeanObject,8842687073059395047 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__15_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__16_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__15_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__14_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__16_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__18_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 35, 91, 95, 44, 93, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__18_value) as *mut crate::leanh::LeanObject,17856333342802343749 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [76, 101, 97, 110, 46, 74, 115, 111, 110, 46, 109, 107, 79, 98, 106, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__25_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 107, 79, 98, 106, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__25_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value) as *mut crate::leanh::LeanObject,849327805763387095 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__25_value) as *mut crate::leanh::LeanObject,1292069500323461113 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__27_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__27_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__29_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 91, 95, 93, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__29_value) as *mut crate::leanh::LeanObject,11666683425613976406 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 74, 115, 111, 110, 46, 110, 117, 109, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value) as *mut crate::leanh::LeanObject,849327805763387095 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_x2d___00__closed__7_value) as *mut crate::leanh::LeanObject,16116999187734878999 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__35_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__36_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__37_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__36_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__35_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__37_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__39_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__39_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__39_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__42_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 101, 114, 109, 45, 95, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__42_value) as *mut crate::leanh::LeanObject,9498589259807162189 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 74, 115, 111, 110, 46, 115, 116, 114, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value) as *mut crate::leanh::LeanObject,849327805763387095 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json___00__closed__2_value) as *mut crate::leanh::LeanObject,17484929713011836251 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__47_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__48_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__49_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__48_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__47_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__49_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 101, 97, 110, 46, 74, 115, 111, 110, 46, 98, 111, 111, 108, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__53_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [98, 111, 111, 108, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__53_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value) as *mut crate::leanh::LeanObject,849327805763387095 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__53_value) as *mut crate::leanh::LeanObject,369595456233876664 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__55_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__56_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__57_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__56_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__57_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__55_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__57_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [66, 111, 111, 108, 46, 102, 97, 108, 115, 101, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61_value) as *mut crate::leanh::LeanObject;
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonFalse___closed__2_value) as *mut crate::leanh::LeanObject,15761733860085307253 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__63_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__63_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__64_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__64_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__65_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__64_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__65_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__63_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__65_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [66, 111, 111, 108, 46, 116, 114, 117, 101, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__61_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonTrue___closed__2_value) as *mut crate::leanh::LeanObject,9255189395584251158 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__70_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__70_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__71_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__71_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__72_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__71_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__70_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__72_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 101, 97, 110, 46, 74, 115, 111, 110, 46, 110, 117, 108, 108, 0]};
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_json_quot___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__0_value) as *mut crate::leanh::LeanObject,849327805763387095 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json_jsonNull___closed__3_value) as *mut crate::leanh::LeanObject,9675591112123903588 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__77_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__77_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__78_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__78_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__79_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__78_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__79: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__79_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__77_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__79_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Parser_Category_json() -> *mut crate::leanh::LeanObject {
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1307_ = crate::leanh::lean_box(0);
    return v___x_1307_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(
    mut v_sz_1537_: usize,
    mut v_i_1538_: usize,
    mut v_bs_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: usize = 0;
    let mut v___x_1550_: usize = 0;
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1541_ = lean_usize_dec_lt(v_i_1538_, v_sz_1537_);
                if v___x_1541_ == 0 {
                    v___x_1542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1542_, 0, v_bs_1539_);
                    crate::leanh::lean_ctor_set(v___x_1542_, 1, v___y_1540_);
                    return v___x_1542_;
                } else {
                    v_v_1543_ = lean_array_uget(v_bs_1539_, v_i_1538_);
                    v___x_1544_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1545_ = lean_array_uset(v_bs_1539_, v_i_1538_, v___x_1544_);
                    v___x_1566_ = l_Lean_Json_jsonIdent___closed__1;
                    crate::leanh::lean_inc(v_v_1543_);
                    v___x_1567_ = l_Lean_Syntax_isOfKind(v_v_1543_, v___x_1566_);
                    if v___x_1567_ == 0 {
                        crate::leanh::lean_dec(v_v_1543_);
                        v___x_1568_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1540_);
                        v___y_1554_ = v___x_1568_;
                        state = 2;
                        continue;
                    } else {
                        v_k_1569_ = l_Lean_Syntax_getArg(v_v_1543_, v___x_1544_);
                        crate::leanh::lean_dec(v_v_1543_);
                        v___x_1570_ = l_Lean_Json_jsonIdent___closed__5;
                        crate::leanh::lean_inc(v_k_1569_);
                        v___x_1571_ = l_Lean_Syntax_isOfKind(v_k_1569_, v___x_1570_);
                        if v___x_1571_ == 0 {
                            v___x_1572_ = l_Lean_Json_json___00__closed__3;
                            crate::leanh::lean_inc(v_k_1569_);
                            v___x_1573_ = l_Lean_Syntax_isOfKind(v_k_1569_, v___x_1572_);
                            if v___x_1573_ == 0 {
                                crate::leanh::lean_dec(v_k_1569_);
                                v___x_1574_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1540_);
                                v___y_1554_ = v___x_1574_;
                                state = 2;
                                continue;
                            } else {
                                v_a_1547_ = v_k_1569_;
                                v_a_1548_ = v___y_1540_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1575_ = l_Lean_TSyntax_getId(v_k_1569_);
                            crate::leanh::lean_dec(v_k_1569_);
                            v___x_1576_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_1575_,
                                    v___x_1571_,
                                );
                            v___x_1577_ = crate::leanh::lean_box(2);
                            v___x_1578_ = l_Lean_Syntax_mkStrLit(v___x_1576_, v___x_1577_);
                            v_a_1547_ = v___x_1578_;
                            v_a_1548_ = v___y_1540_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1549_ = 1usize;
                v___x_1550_ = lean_usize_add(v_i_1538_, v___x_1549_);
                v___x_1551_ = lean_array_uset(v_bs_x27_1545_, v_i_1538_, v_a_1547_);
                v_i_1538_ = v___x_1550_;
                v_bs_1539_ = v___x_1551_;
                v___y_1540_ = v_a_1548_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1554_) == 0 {
                    v_a_1555_ = crate::leanh::lean_ctor_get(v___y_1554_, 0);
                    crate::leanh::lean_inc(v_a_1555_);
                    v_a_1556_ = crate::leanh::lean_ctor_get(v___y_1554_, 1);
                    crate::leanh::lean_inc(v_a_1556_);
                    crate::leanh::lean_dec_ref_known(v___y_1554_, 2);
                    v_a_1547_ = v_a_1555_;
                    v_a_1548_ = v_a_1556_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_1545_);
                    v_a_1557_ = crate::leanh::lean_ctor_get(v___y_1554_, 0);
                    v_a_1558_ = crate::leanh::lean_ctor_get(v___y_1554_, 1);
                    v_isSharedCheck_1565_ = (!crate::leanh::lean_is_exclusive(v___y_1554_)) as u8;
                    if v_isSharedCheck_1565_ == 0 {
                        v___x_1560_ = v___y_1554_;
                        v_isShared_1561_ = v_isSharedCheck_1565_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1558_);
                        crate::leanh::lean_inc(v_a_1557_);
                        crate::leanh::lean_dec(v___y_1554_);
                        v___x_1560_ = crate::leanh::lean_box(0);
                        v_isShared_1561_ = v_isSharedCheck_1565_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1561_ == 0 {
                    v___x_1563_ = v___x_1560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1564_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1557_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_a_1558_);
                    v___x_1563_ = v_reuseFailAlloc_1564_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg___boxed(
    mut v_sz_1579_: *mut crate::leanh::LeanObject,
    mut v_i_1580_: *mut crate::leanh::LeanObject,
    mut v_bs_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1583_: usize = 0;
    let mut v_i_boxed_1584_: usize = 0;
    let mut v_res_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1583_ = crate::leanh::lean_unbox_usize(v_sz_1579_);
    crate::leanh::lean_dec(v_sz_1579_);
    v_i_boxed_1584_ = crate::leanh::lean_unbox_usize(v_i_1580_);
    crate::leanh::lean_dec(v_i_1580_);
    v_res_1585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(v_sz_boxed_1583_, v_i_boxed_1584_, v_bs_1581_, v___y_1582_);
    return v_res_1585_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(
    mut v_sz_1586_: usize,
    mut v_i_1587_: usize,
    mut v_bs_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: u8 = 0;
    let mut v_v_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: usize = 0;
    let mut v___x_1595_: usize = 0;
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1589_ = lean_usize_dec_lt(v_i_1587_, v_sz_1586_);
                if v___x_1589_ == 0 {
                    return v_bs_1588_;
                } else {
                    v_v_1590_ = lean_array_uget_borrowed(v_bs_1588_, v_i_1587_);
                    v_fst_1591_ = crate::leanh::lean_ctor_get(v_v_1590_, 0);
                    crate::leanh::lean_inc(v_fst_1591_);
                    v___x_1592_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1593_ = lean_array_uset(v_bs_1588_, v_i_1587_, v___x_1592_);
                    v___x_1594_ = 1usize;
                    v___x_1595_ = lean_usize_add(v_i_1587_, v___x_1594_);
                    v___x_1596_ = lean_array_uset(v_bs_x27_1593_, v_i_1587_, v_fst_1591_);
                    v_i_1587_ = v___x_1595_;
                    v_bs_1588_ = v___x_1596_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2___boxed(
    mut v_sz_1598_: *mut crate::leanh::LeanObject,
    mut v_i_1599_: *mut crate::leanh::LeanObject,
    mut v_bs_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1601_: usize = 0;
    let mut v_i_boxed_1602_: usize = 0;
    let mut v_res_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1601_ = crate::leanh::lean_unbox_usize(v_sz_1598_);
    crate::leanh::lean_dec(v_sz_1598_);
    v_i_boxed_1602_ = crate::leanh::lean_unbox_usize(v_i_1599_);
    crate::leanh::lean_dec(v_i_1599_);
    v_res_1603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v_sz_boxed_1601_, v_i_boxed_1602_, v_bs_1600_);
    return v_res_1603_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__8;
    v___x_1624_ = l_String_toRawSubstring_x27(v___x_1623_);
    return v___x_1624_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(
    mut v___x_1634_: *mut crate::leanh::LeanObject,
    mut v___x_1635_: *mut crate::leanh::LeanObject,
    mut v___x_1636_: *mut crate::leanh::LeanObject,
    mut v_sz_1637_: usize,
    mut v_i_1638_: usize,
    mut v_bs_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: u8 = 0;
    let mut v_v_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1646_: u8 = 0;
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: usize = 0;
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1640_ = lean_usize_dec_lt(v_i_1638_, v_sz_1637_);
                if v___x_1640_ == 0 {
                    crate::leanh::lean_dec(v___x_1636_);
                    crate::leanh::lean_dec(v___x_1635_);
                    crate::leanh::lean_dec(v___x_1634_);
                    return v_bs_1639_;
                } else {
                    v_v_1641_ = lean_array_uget(v_bs_1639_, v_i_1638_);
                    v_fst_1642_ = crate::leanh::lean_ctor_get(v_v_1641_, 0);
                    v_snd_1643_ = crate::leanh::lean_ctor_get(v_v_1641_, 1);
                    v_isSharedCheck_1679_ = (!crate::leanh::lean_is_exclusive(v_v_1641_)) as u8;
                    if v_isSharedCheck_1679_ == 0 {
                        v___x_1645_ = v_v_1641_;
                        v_isShared_1646_ = v_isSharedCheck_1679_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1643_);
                        crate::leanh::lean_inc(v_fst_1642_);
                        crate::leanh::lean_dec(v_v_1641_);
                        v___x_1645_ = crate::leanh::lean_box(0);
                        v_isShared_1646_ = v_isSharedCheck_1679_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1647_ = l_Lean_Json_termJson_x25___00__closed__1;
                v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                v___x_1649_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_1650_ = lean_array_uset(v_bs_1639_, v_i_1638_, v___x_1649_);
                v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__2;
                v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4;
                v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5;
                crate::leanh::lean_inc(v___x_1634_);
                if v_isShared_1646_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1645_, 2);
                    crate::leanh::lean_ctor_set(v___x_1645_, 1, v___x_1653_);
                    crate::leanh::lean_ctor_set(v___x_1645_, 0, v___x_1634_);
                    v___x_1655_ = v___x_1645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1678_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1653_);
                    v___x_1655_ = v_reuseFailAlloc_1678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7;
                v___x_1657_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9);
                v___x_1658_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_1636_);
                crate::leanh::lean_inc(v___x_1635_);
                v___x_1659_ = l_Lean_addMacroScope(v___x_1635_, v___x_1658_, v___x_1636_);
                v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__12;
                crate::leanh::lean_inc_n(v___x_1634_, 10);
                v___x_1661_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1661_, 0, v___x_1634_);
                crate::leanh::lean_ctor_set(v___x_1661_, 1, v___x_1657_);
                crate::leanh::lean_ctor_set(v___x_1661_, 2, v___x_1659_);
                crate::leanh::lean_ctor_set(v___x_1661_, 3, v___x_1660_);
                v___x_1662_ = l_Lean_Syntax_node1(v___x_1634_, v___x_1656_, v___x_1661_);
                v___x_1663_ =
                    l_Lean_Syntax_node2(v___x_1634_, v___x_1652_, v___x_1655_, v___x_1662_);
                v___x_1664_ = l_Lean_Json_json_x5b___x5d___closed__4;
                v___x_1665_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1634_);
                crate::leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                v___x_1666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13;
                v___x_1667_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1634_);
                crate::leanh::lean_ctor_set(v___x_1667_, 1, v___x_1666_);
                v___x_1668_ =
                    l_Lean_Syntax_node2(v___x_1634_, v___x_1647_, v___x_1667_, v_snd_1643_);
                v___x_1669_ = l_Lean_Syntax_node1(v___x_1634_, v___x_1648_, v___x_1668_);
                v___x_1670_ = l_Lean_Syntax_node3(
                    v___x_1634_,
                    v___x_1648_,
                    v_fst_1642_,
                    v___x_1665_,
                    v___x_1669_,
                );
                v___x_1671_ = l_Lean_Json_json_quot___closed__13;
                v___x_1672_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1672_, 0, v___x_1634_);
                crate::leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                v___x_1673_ = l_Lean_Syntax_node3(
                    v___x_1634_,
                    v___x_1651_,
                    v___x_1663_,
                    v___x_1670_,
                    v___x_1672_,
                );
                v___x_1674_ = 1usize;
                v___x_1675_ = lean_usize_add(v_i_1638_, v___x_1674_);
                v___x_1676_ = lean_array_uset(v_bs_x27_1650_, v_i_1638_, v___x_1673_);
                v_i_1638_ = v___x_1675_;
                v_bs_1639_ = v___x_1676_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___boxed(
    mut v___x_1680_: *mut crate::leanh::LeanObject,
    mut v___x_1681_: *mut crate::leanh::LeanObject,
    mut v___x_1682_: *mut crate::leanh::LeanObject,
    mut v_sz_1683_: *mut crate::leanh::LeanObject,
    mut v_i_1684_: *mut crate::leanh::LeanObject,
    mut v_bs_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1686_: usize = 0;
    let mut v_i_boxed_1687_: usize = 0;
    let mut v_res_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1686_ = crate::leanh::lean_unbox_usize(v_sz_1683_);
    crate::leanh::lean_dec(v_sz_1683_);
    v_i_boxed_1687_ = crate::leanh::lean_unbox_usize(v_i_1684_);
    crate::leanh::lean_dec(v_i_1684_);
    v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v___x_1680_, v___x_1681_, v___x_1682_, v_sz_boxed_1686_, v_i_boxed_1687_, v_bs_1685_);
    return v_res_1688_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(
    mut v_sz_1689_: usize,
    mut v_i_1690_: usize,
    mut v_bs_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: usize = 0;
    let mut v___x_1698_: usize = 0;
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1692_ = lean_usize_dec_lt(v_i_1690_, v_sz_1689_);
                if v___x_1692_ == 0 {
                    v___x_1693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1693_, 0, v_bs_1691_);
                    return v___x_1693_;
                } else {
                    v_v_1694_ = lean_array_uget(v_bs_1691_, v_i_1690_);
                    v___x_1695_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1696_ = lean_array_uset(v_bs_1691_, v_i_1690_, v___x_1695_);
                    v___x_1697_ = 1usize;
                    v___x_1698_ = lean_usize_add(v_i_1690_, v___x_1697_);
                    v___x_1699_ = lean_array_uset(v_bs_x27_1696_, v_i_1690_, v_v_1694_);
                    v_i_1690_ = v___x_1698_;
                    v_bs_1691_ = v___x_1699_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6___boxed(
    mut v_sz_1701_: *mut crate::leanh::LeanObject,
    mut v_i_1702_: *mut crate::leanh::LeanObject,
    mut v_bs_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1704_: usize = 0;
    let mut v_i_boxed_1705_: usize = 0;
    let mut v_res_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1704_ = crate::leanh::lean_unbox_usize(v_sz_1701_);
    crate::leanh::lean_dec(v_sz_1701_);
    v_i_boxed_1705_ = crate::leanh::lean_unbox_usize(v_i_1702_);
    crate::leanh::lean_dec(v_i_1702_);
    v_res_1706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v_sz_boxed_1704_, v_i_boxed_1705_, v_bs_1703_);
    return v_res_1706_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(
    mut v___x_1707_: u8,
    mut v___x_1708_: u8,
    mut v_as_1709_: *mut crate::leanh::LeanObject,
    mut v_i_1710_: usize,
    mut v_stop_1711_: usize,
    mut v_b_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: usize = 0;
    let mut v___x_1716_: usize = 0;
    let mut v___x_1718_: u8 = 0;
    let mut v_fst_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v_snd_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1724_: u8 = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut v_unused_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_unused_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1718_ = lean_usize_dec_eq(v_i_1710_, v_stop_1711_);
                if v___x_1718_ == 0 {
                    v_fst_1719_ = crate::leanh::lean_ctor_get(v_b_1712_, 0);
                    v___x_1720_ = (crate::leanh::lean_unbox(v_fst_1719_) as u8);
                    if v___x_1720_ == 0 {
                        v_snd_1721_ = crate::leanh::lean_ctor_get(v_b_1712_, 1);
                        v_isSharedCheck_1729_ = (!crate::leanh::lean_is_exclusive(v_b_1712_)) as u8;
                        if v_isSharedCheck_1729_ == 0 {
                            v_unused_1730_ = crate::leanh::lean_ctor_get(v_b_1712_, 0);
                            crate::leanh::lean_dec(v_unused_1730_);
                            v___x_1723_ = v_b_1712_;
                            v_isShared_1724_ = v_isSharedCheck_1729_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1721_);
                            crate::leanh::lean_dec(v_b_1712_);
                            v___x_1723_ = crate::leanh::lean_box(0);
                            v_isShared_1724_ = v_isSharedCheck_1729_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_1731_ = crate::leanh::lean_ctor_get(v_b_1712_, 1);
                        v_isSharedCheck_1741_ = (!crate::leanh::lean_is_exclusive(v_b_1712_)) as u8;
                        if v_isSharedCheck_1741_ == 0 {
                            v_unused_1742_ = crate::leanh::lean_ctor_get(v_b_1712_, 0);
                            crate::leanh::lean_dec(v_unused_1742_);
                            v___x_1733_ = v_b_1712_;
                            v_isShared_1734_ = v_isSharedCheck_1741_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1731_);
                            crate::leanh::lean_dec(v_b_1712_);
                            v___x_1733_ = crate::leanh::lean_box(0);
                            v_isShared_1734_ = v_isSharedCheck_1741_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_1712_;
                }
            }
            1 => {
                v___x_1715_ = 1usize;
                v___x_1716_ = lean_usize_add(v_i_1710_, v___x_1715_);
                v_i_1710_ = v___x_1716_;
                v_b_1712_ = v___y_1714_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1725_ = crate::leanh::lean_box((v___x_1707_) as usize);
                if v_isShared_1724_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1723_, 0, v___x_1725_);
                    v___x_1727_ = v___x_1723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_snd_1721_);
                    v___x_1727_ = v_reuseFailAlloc_1728_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1714_ = v___x_1727_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1735_ = lean_array_uget_borrowed(v_as_1709_, v_i_1710_);
                crate::leanh::lean_inc(v___x_1735_);
                v___x_1736_ = lean_array_push(v_snd_1731_, v___x_1735_);
                v___x_1737_ = crate::leanh::lean_box((v___x_1708_) as usize);
                if v_isShared_1734_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1733_, 1, v___x_1736_);
                    crate::leanh::lean_ctor_set(v___x_1733_, 0, v___x_1737_);
                    v___x_1739_ = v___x_1733_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 1, v___x_1736_);
                    v___x_1739_ = v_reuseFailAlloc_1740_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1714_ = v___x_1739_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5___boxed(
    mut v___x_1743_: *mut crate::leanh::LeanObject,
    mut v___x_1744_: *mut crate::leanh::LeanObject,
    mut v_as_1745_: *mut crate::leanh::LeanObject,
    mut v_i_1746_: *mut crate::leanh::LeanObject,
    mut v_stop_1747_: *mut crate::leanh::LeanObject,
    mut v_b_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_67873__boxed_1749_: u8 = 0;
    let mut v___x_67874__boxed_1750_: u8 = 0;
    let mut v_i_boxed_1751_: usize = 0;
    let mut v_stop_boxed_1752_: usize = 0;
    let mut v_res_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_67873__boxed_1749_ = (crate::leanh::lean_unbox(v___x_1743_) as u8);
    v___x_67874__boxed_1750_ = (crate::leanh::lean_unbox(v___x_1744_) as u8);
    v_i_boxed_1751_ = crate::leanh::lean_unbox_usize(v_i_1746_);
    crate::leanh::lean_dec(v_i_1746_);
    v_stop_boxed_1752_ = crate::leanh::lean_unbox_usize(v_stop_1747_);
    crate::leanh::lean_dec(v_stop_1747_);
    v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_67873__boxed_1749_, v___x_67874__boxed_1750_, v_as_1745_, v_i_boxed_1751_, v_stop_boxed_1752_, v_b_1748_);
    crate::leanh::lean_dec_ref(v_as_1745_);
    return v_res_1753_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(
    mut v_sz_1754_: usize,
    mut v_i_1755_: usize,
    mut v_bs_1756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: usize = 0;
    let mut v___x_1773_: usize = 0;
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1757_ = lean_usize_dec_lt(v_i_1755_, v_sz_1754_);
                if v___x_1757_ == 0 {
                    v___x_1758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1758_, 0, v_bs_1756_);
                    return v___x_1758_;
                } else {
                    v_v_1759_ = lean_array_uget(v_bs_1756_, v_i_1755_);
                    v___x_1760_ = l_Lean_Json_jsonField___closed__1;
                    crate::leanh::lean_inc(v_v_1759_);
                    v___x_1761_ = l_Lean_Syntax_isOfKind(v_v_1759_, v___x_1760_);
                    if v___x_1761_ == 0 {
                        crate::leanh::lean_dec(v_v_1759_);
                        crate::leanh::lean_dec_ref(v_bs_1756_);
                        v___x_1762_ = crate::leanh::lean_box(0);
                        return v___x_1762_;
                    } else {
                        v___x_1763_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_ks_1764_ = l_Lean_Syntax_getArg(v_v_1759_, v___x_1763_);
                        v___x_1765_ = l_Lean_Json_jsonIdent___closed__1;
                        crate::leanh::lean_inc(v_ks_1764_);
                        v___x_1766_ = l_Lean_Syntax_isOfKind(v_ks_1764_, v___x_1765_);
                        if v___x_1766_ == 0 {
                            crate::leanh::lean_dec(v_ks_1764_);
                            crate::leanh::lean_dec(v_v_1759_);
                            crate::leanh::lean_dec_ref(v_bs_1756_);
                            v___x_1767_ = crate::leanh::lean_box(0);
                            return v___x_1767_;
                        } else {
                            v_bs_x27_1768_ = lean_array_uset(v_bs_1756_, v_i_1755_, v___x_1763_);
                            v___x_1769_ = crate::leanh::lean_unsigned_to_nat(2);
                            v_vs_1770_ = l_Lean_Syntax_getArg(v_v_1759_, v___x_1769_);
                            crate::leanh::lean_dec(v_v_1759_);
                            v___x_1771_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1771_, 0, v_ks_1764_);
                            crate::leanh::lean_ctor_set(v___x_1771_, 1, v_vs_1770_);
                            v___x_1772_ = 1usize;
                            v___x_1773_ = lean_usize_add(v_i_1755_, v___x_1772_);
                            v___x_1774_ = lean_array_uset(v_bs_x27_1768_, v_i_1755_, v___x_1771_);
                            v_i_1755_ = v___x_1773_;
                            v_bs_1756_ = v___x_1774_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0___boxed(
    mut v_sz_1776_: *mut crate::leanh::LeanObject,
    mut v_i_1777_: *mut crate::leanh::LeanObject,
    mut v_bs_1778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1779_: usize = 0;
    let mut v_i_boxed_1780_: usize = 0;
    let mut v_res_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1779_ = crate::leanh::lean_unbox_usize(v_sz_1776_);
    crate::leanh::lean_dec(v_sz_1776_);
    v_i_boxed_1780_ = crate::leanh::lean_unbox_usize(v_i_1777_);
    crate::leanh::lean_dec(v_i_1777_);
    v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_boxed_1779_, v_i_boxed_1780_, v_bs_1778_);
    return v_res_1781_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(
    mut v___x_1782_: *mut crate::leanh::LeanObject,
    mut v_sz_1783_: usize,
    mut v_i_1784_: usize,
    mut v_bs_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: usize = 0;
    let mut v___x_1795_: usize = 0;
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1786_ = lean_usize_dec_lt(v_i_1784_, v_sz_1783_);
                if v___x_1786_ == 0 {
                    crate::leanh::lean_dec(v___x_1782_);
                    return v_bs_1785_;
                } else {
                    v___x_1787_ = l_Lean_Json_termJson_x25___00__closed__1;
                    v_v_1788_ = lean_array_uget(v_bs_1785_, v_i_1784_);
                    v___x_1789_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1790_ = lean_array_uset(v_bs_1785_, v_i_1784_, v___x_1789_);
                    v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__13;
                    crate::leanh::lean_inc_n(v___x_1782_, 2);
                    v___x_1792_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1792_, 0, v___x_1782_);
                    crate::leanh::lean_ctor_set(v___x_1792_, 1, v___x_1791_);
                    v___x_1793_ =
                        l_Lean_Syntax_node2(v___x_1782_, v___x_1787_, v___x_1792_, v_v_1788_);
                    v___x_1794_ = 1usize;
                    v___x_1795_ = lean_usize_add(v_i_1784_, v___x_1794_);
                    v___x_1796_ = lean_array_uset(v_bs_x27_1790_, v_i_1784_, v___x_1793_);
                    v_i_1784_ = v___x_1795_;
                    v_bs_1785_ = v___x_1796_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7___boxed(
    mut v___x_1798_: *mut crate::leanh::LeanObject,
    mut v_sz_1799_: *mut crate::leanh::LeanObject,
    mut v_i_1800_: *mut crate::leanh::LeanObject,
    mut v_bs_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1802_: usize = 0;
    let mut v_i_boxed_1803_: usize = 0;
    let mut v_res_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1802_ = crate::leanh::lean_unbox_usize(v_sz_1799_);
    crate::leanh::lean_dec(v_sz_1799_);
    v_i_boxed_1803_ = crate::leanh::lean_unbox_usize(v_i_1800_);
    crate::leanh::lean_dec(v_i_1800_);
    v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_1798_, v_sz_boxed_1802_, v_i_boxed_1803_, v_bs_1801_);
    return v_res_1804_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(
    mut v_sz_1805_: usize,
    mut v_i_1806_: usize,
    mut v_bs_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1808_: u8 = 0;
    let mut v_v_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: usize = 0;
    let mut v___x_1814_: usize = 0;
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1808_ = lean_usize_dec_lt(v_i_1806_, v_sz_1805_);
                if v___x_1808_ == 0 {
                    return v_bs_1807_;
                } else {
                    v_v_1809_ = lean_array_uget_borrowed(v_bs_1807_, v_i_1806_);
                    v_snd_1810_ = crate::leanh::lean_ctor_get(v_v_1809_, 1);
                    crate::leanh::lean_inc(v_snd_1810_);
                    v___x_1811_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1812_ = lean_array_uset(v_bs_1807_, v_i_1806_, v___x_1811_);
                    v___x_1813_ = 1usize;
                    v___x_1814_ = lean_usize_add(v_i_1806_, v___x_1813_);
                    v___x_1815_ = lean_array_uset(v_bs_x27_1812_, v_i_1806_, v_snd_1810_);
                    v_i_1806_ = v___x_1814_;
                    v_bs_1807_ = v___x_1815_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1___boxed(
    mut v_sz_1817_: *mut crate::leanh::LeanObject,
    mut v_i_1818_: *mut crate::leanh::LeanObject,
    mut v_bs_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1820_: usize = 0;
    let mut v_i_boxed_1821_: usize = 0;
    let mut v_res_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1820_ = crate::leanh::lean_unbox_usize(v_sz_1817_);
    crate::leanh::lean_dec(v_sz_1817_);
    v_i_boxed_1821_ = crate::leanh::lean_unbox_usize(v_i_1818_);
    crate::leanh::lean_dec(v_i_1818_);
    v_res_1822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v_sz_boxed_1820_, v_i_boxed_1821_, v_bs_1819_);
    return v_res_1822_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__2;
    v___x_1831_ = l_String_toRawSubstring_x27(v___x_1830_);
    return v___x_1831_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__10;
    v___x_1849_ = l_String_toRawSubstring_x27(v___x_1848_);
    return v___x_1849_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1870_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = l_Lean_Json_json_x5b___x5d___closed__4;
    v___x_1872_ = l_Lean_mkAtom(v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__23;
    v___x_1875_ = l_String_toRawSubstring_x27(v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__32;
    v___x_1894_ = l_String_toRawSubstring_x27(v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__44;
    v___x_1924_ = l_String_toRawSubstring_x27(v___x_1923_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__51;
    v___x_1942_ = l_String_toRawSubstring_x27(v___x_1941_);
    return v___x_1942_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__59;
    v___x_1961_ = l_String_toRawSubstring_x27(v___x_1960_);
    return v___x_1961_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1978_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__67;
    v___x_1979_ = l_String_toRawSubstring_x27(v___x_1978_);
    return v___x_1979_;
}
pub unsafe fn _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__74;
    v___x_1996_ = l_String_toRawSubstring_x27(v___x_1995_);
    return v___x_1996_;
}
pub unsafe fn l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(
    mut v_x_2012_: *mut crate::leanh::LeanObject,
    mut v_a_2013_: *mut crate::leanh::LeanObject,
    mut v_a_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: u8 = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___y_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2036_: usize = 0;
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2072_: usize = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: u8 = 0;
    let mut v___y_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2088_: usize = 0;
    let mut v___x_2089_: usize = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2109_: usize = 0;
    let mut v_vs_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2112_: usize = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2118_: u8 = 0;
    let mut v_quotContext_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2135_: usize = 0;
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut v_a_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: u8 = 0;
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: usize = 0;
    let mut v___x_2187_: usize = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: usize = 0;
    let mut v___x_2191_: usize = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: u8 = 0;
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: usize = 0;
    let mut v___x_2207_: usize = 0;
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: u8 = 0;
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: u8 = 0;
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2393_: u8 = 0;
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: u8 = 0;
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2015_ = l_Lean_Json_termJson_x25___00__closed__1;
                crate::leanh::lean_inc(v_x_2012_);
                v___x_2016_ = l_Lean_Syntax_isOfKind(v_x_2012_, v___x_2015_);
                if v___x_2016_ == 0 {
                    crate::leanh::lean_dec(v_x_2012_);
                    v___x_2017_ = crate::leanh::lean_box(1);
                    v___x_2018_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2018_, 0, v___x_2017_);
                    crate::leanh::lean_ctor_set(v___x_2018_, 1, v_a_2014_);
                    return v___x_2018_;
                } else {
                    v___x_2019_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2020_ = l_Lean_Syntax_getArg(v_x_2012_, v___x_2019_);
                    crate::leanh::lean_dec(v_x_2012_);
                    v___x_2021_ = l_Lean_Json_jsonNull___closed__2;
                    crate::leanh::lean_inc(v___x_2020_);
                    v___x_2022_ = l_Lean_Syntax_isOfKind(v___x_2020_, v___x_2021_);
                    if v___x_2022_ == 0 {
                        v___x_2023_ = l_Lean_Json_jsonTrue___closed__1;
                        crate::leanh::lean_inc(v___x_2020_);
                        v___x_2024_ = l_Lean_Syntax_isOfKind(v___x_2020_, v___x_2023_);
                        if v___x_2024_ == 0 {
                            v___x_2025_ = l_Lean_Json_jsonFalse___closed__1;
                            crate::leanh::lean_inc(v___x_2020_);
                            v___x_2026_ = l_Lean_Syntax_isOfKind(v___x_2020_, v___x_2025_);
                            if v___x_2026_ == 0 {
                                v___x_2027_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_2028_ = l_Lean_Json_json___00__closed__1;
                                crate::leanh::lean_inc(v___x_2020_);
                                v___x_2029_ = l_Lean_Syntax_isOfKind(v___x_2020_, v___x_2028_);
                                if v___x_2029_ == 0 {
                                    v___x_2030_ = l_Lean_Json_json_x2d___00__closed__1;
                                    crate::leanh::lean_inc(v___x_2020_);
                                    v___x_2031_ = l_Lean_Syntax_isOfKind(v___x_2020_, v___x_2030_);
                                    if v___x_2031_ == 0 {
                                        v___x_2032_ = l_Lean_Json_json_x2d____1___closed__1;
                                        crate::leanh::lean_inc(v___x_2020_);
                                        v___x_2033_ =
                                            l_Lean_Syntax_isOfKind(v___x_2020_, v___x_2032_);
                                        if v___x_2033_ == 0 {
                                            v___x_2084_ = l_Lean_Json_json_x5b___x5d___closed__1;
                                            crate::leanh::lean_inc(v___x_2020_);
                                            v___x_2085_ =
                                                l_Lean_Syntax_isOfKind(v___x_2020_, v___x_2084_);
                                            if v___x_2085_ == 0 {
                                                v___x_2159_ =
                                                    l_Lean_Json_json_x7b___x7d___closed__1;
                                                crate::leanh::lean_inc(v___x_2020_);
                                                v___x_2160_ = l_Lean_Syntax_isOfKind(
                                                    v___x_2020_,
                                                    v___x_2159_,
                                                );
                                                if v___x_2160_ == 0 {
                                                    v___x_2161_ =
                                                        l_Lean_Syntax_isAntiquot(v___x_2020_);
                                                    if v___x_2161_ == 0 {
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v___x_2162_ =
                                                            l_Lean_Macro_throwUnsupported___redArg(
                                                                v_a_2014_,
                                                            );
                                                        return v___x_2162_;
                                                    } else {
                                                        v_quotContext_2163_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 1,
                                                            );
                                                        v_currMacroScope_2164_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 2,
                                                            );
                                                        v_ref_2165_ = crate::leanh::lean_ctor_get(
                                                            v_a_2013_, 5,
                                                        );
                                                        v___x_2166_ = l_Lean_Syntax_getAntiquotTerm(
                                                            v___x_2020_,
                                                        );
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v___x_2167_ = l_Lean_SourceInfo_fromRef(
                                                            v_ref_2165_,
                                                            v___x_2160_,
                                                        );
                                                        v___x_2168_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                        v___x_2169_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                                                        v___x_2170_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                                                        crate::leanh::lean_inc(
                                                            v_currMacroScope_2164_,
                                                        );
                                                        crate::leanh::lean_inc(v_quotContext_2163_);
                                                        v___x_2171_ = l_Lean_addMacroScope(
                                                            v_quotContext_2163_,
                                                            v___x_2170_,
                                                            v_currMacroScope_2164_,
                                                        );
                                                        v___x_2172_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                                                        crate::leanh::lean_inc_n(v___x_2167_, 2);
                                                        v___x_2173_ = crate::leanh::lean_alloc_ctor(
                                                            3,
                                                            4,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2173_,
                                                            0,
                                                            v___x_2167_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2173_,
                                                            1,
                                                            v___x_2169_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2173_,
                                                            2,
                                                            v___x_2171_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2173_,
                                                            3,
                                                            v___x_2172_,
                                                        );
                                                        v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                        v___x_2175_ = l_Lean_Syntax_node1(
                                                            v___x_2167_,
                                                            v___x_2174_,
                                                            v___x_2166_,
                                                        );
                                                        v___x_2176_ = l_Lean_Syntax_node2(
                                                            v___x_2167_,
                                                            v___x_2168_,
                                                            v___x_2173_,
                                                            v___x_2175_,
                                                        );
                                                        v___x_2177_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2177_,
                                                            0,
                                                            v___x_2176_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2177_,
                                                            1,
                                                            v_a_2014_,
                                                        );
                                                        return v___x_2177_;
                                                    }
                                                } else {
                                                    v___x_2178_ = l_Lean_Syntax_getArg(
                                                        v___x_2020_,
                                                        v___x_2019_,
                                                    );
                                                    v___x_2179_ =
                                                        l_Lean_Syntax_getArgs(v___x_2178_);
                                                    crate::leanh::lean_dec(v___x_2178_);
                                                    v___x_2180_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31;
                                                    v___x_2181_ = lean_array_get_size(v___x_2179_);
                                                    v___x_2182_ =
                                                        lean_nat_dec_lt(v___x_2027_, v___x_2181_);
                                                    if v___x_2182_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_2179_);
                                                        v___y_2087_ = v___x_2180_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v___x_2183_ = crate::leanh::lean_box(
                                                            (v___x_2160_) as usize,
                                                        );
                                                        v___x_2184_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2184_,
                                                            0,
                                                            v___x_2183_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2184_,
                                                            1,
                                                            v___x_2180_,
                                                        );
                                                        v___x_2185_ = lean_nat_dec_le(
                                                            v___x_2181_,
                                                            v___x_2181_,
                                                        );
                                                        if v___x_2185_ == 0 {
                                                            if v___x_2182_ == 0 {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_2184_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2179_,
                                                                );
                                                                v___y_2087_ = v___x_2180_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                v___x_2186_ = 0usize;
                                                                v___x_2187_ =
                                                                    lean_usize_of_nat(v___x_2181_);
                                                                v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_2160_, v___x_2085_, v___x_2179_, v___x_2186_, v___x_2187_, v___x_2184_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2179_,
                                                                );
                                                                v_snd_2189_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_2188_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc(v_snd_2189_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2188_,
                                                                );
                                                                v___y_2087_ = v_snd_2189_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            v___x_2190_ = 0usize;
                                                            v___x_2191_ =
                                                                lean_usize_of_nat(v___x_2181_);
                                                            v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_2160_, v___x_2085_, v___x_2179_, v___x_2190_, v___x_2191_, v___x_2184_);
                                                            crate::leanh::lean_dec_ref(v___x_2179_);
                                                            v_snd_2193_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v___x_2192_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_inc(v_snd_2193_);
                                                            crate::leanh::lean_dec_ref(v___x_2192_);
                                                            v___y_2087_ = v_snd_2193_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                v___x_2194_ =
                                                    l_Lean_Syntax_getArg(v___x_2020_, v___x_2019_);
                                                v___x_2195_ = l_Lean_Syntax_getArgs(v___x_2194_);
                                                crate::leanh::lean_dec(v___x_2194_);
                                                v___x_2196_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__31;
                                                v___x_2197_ = lean_array_get_size(v___x_2195_);
                                                v___x_2198_ =
                                                    lean_nat_dec_lt(v___x_2027_, v___x_2197_);
                                                if v___x_2198_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_2195_);
                                                    v___y_2035_ = v___x_2196_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_2199_ = crate::leanh::lean_box(
                                                        (v___x_2085_) as usize,
                                                    );
                                                    v___x_2200_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2200_,
                                                        0,
                                                        v___x_2199_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2200_,
                                                        1,
                                                        v___x_2196_,
                                                    );
                                                    v___x_2201_ =
                                                        lean_nat_dec_le(v___x_2197_, v___x_2197_);
                                                    if v___x_2201_ == 0 {
                                                        if v___x_2198_ == 0 {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_2200_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec_ref(v___x_2195_);
                                                            v___y_2035_ = v___x_2196_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_2202_ = 0usize;
                                                            v___x_2203_ =
                                                                lean_usize_of_nat(v___x_2197_);
                                                            v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_2085_, v___x_2033_, v___x_2195_, v___x_2202_, v___x_2203_, v___x_2200_);
                                                            crate::leanh::lean_dec_ref(v___x_2195_);
                                                            v_snd_2205_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v___x_2204_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_inc(v_snd_2205_);
                                                            crate::leanh::lean_dec_ref(v___x_2204_);
                                                            v___y_2035_ = v_snd_2205_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        v___x_2206_ = 0usize;
                                                        v___x_2207_ =
                                                            lean_usize_of_nat(v___x_2197_);
                                                        v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__5(v___x_2085_, v___x_2033_, v___x_2195_, v___x_2206_, v___x_2207_, v___x_2200_);
                                                        crate::leanh::lean_dec_ref(v___x_2195_);
                                                        v_snd_2209_ = crate::leanh::lean_ctor_get(
                                                            v___x_2208_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc(v_snd_2209_);
                                                        crate::leanh::lean_dec_ref(v___x_2208_);
                                                        v___y_2035_ = v_snd_2209_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            v___x_2210_ =
                                                l_Lean_Syntax_getArg(v___x_2020_, v___x_2027_);
                                            crate::leanh::lean_inc(v___x_2210_);
                                            v___x_2211_ =
                                                l_Lean_Syntax_matchesNull(v___x_2210_, v___x_2027_);
                                            if v___x_2211_ == 0 {
                                                v___x_2212_ = l_Lean_Syntax_matchesNull(
                                                    v___x_2210_,
                                                    v___x_2019_,
                                                );
                                                if v___x_2212_ == 0 {
                                                    v___x_2213_ =
                                                        l_Lean_Syntax_isAntiquot(v___x_2020_);
                                                    if v___x_2213_ == 0 {
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v___x_2214_ =
                                                            l_Lean_Macro_throwUnsupported___redArg(
                                                                v_a_2014_,
                                                            );
                                                        return v___x_2214_;
                                                    } else {
                                                        v_quotContext_2215_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 1,
                                                            );
                                                        v_currMacroScope_2216_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 2,
                                                            );
                                                        v_ref_2217_ = crate::leanh::lean_ctor_get(
                                                            v_a_2013_, 5,
                                                        );
                                                        v___x_2218_ = l_Lean_Syntax_getAntiquotTerm(
                                                            v___x_2020_,
                                                        );
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v___x_2219_ = l_Lean_SourceInfo_fromRef(
                                                            v_ref_2217_,
                                                            v___x_2212_,
                                                        );
                                                        v___x_2220_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                        v___x_2221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                                                        v___x_2222_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                                                        crate::leanh::lean_inc(
                                                            v_currMacroScope_2216_,
                                                        );
                                                        crate::leanh::lean_inc(v_quotContext_2215_);
                                                        v___x_2223_ = l_Lean_addMacroScope(
                                                            v_quotContext_2215_,
                                                            v___x_2222_,
                                                            v_currMacroScope_2216_,
                                                        );
                                                        v___x_2224_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                                                        crate::leanh::lean_inc_n(v___x_2219_, 2);
                                                        v___x_2225_ = crate::leanh::lean_alloc_ctor(
                                                            3,
                                                            4,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2225_,
                                                            0,
                                                            v___x_2219_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2225_,
                                                            1,
                                                            v___x_2221_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2225_,
                                                            2,
                                                            v___x_2223_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2225_,
                                                            3,
                                                            v___x_2224_,
                                                        );
                                                        v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                        v___x_2227_ = l_Lean_Syntax_node1(
                                                            v___x_2219_,
                                                            v___x_2226_,
                                                            v___x_2218_,
                                                        );
                                                        v___x_2228_ = l_Lean_Syntax_node2(
                                                            v___x_2219_,
                                                            v___x_2220_,
                                                            v___x_2225_,
                                                            v___x_2227_,
                                                        );
                                                        v___x_2229_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2229_,
                                                            0,
                                                            v___x_2228_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2229_,
                                                            1,
                                                            v_a_2014_,
                                                        );
                                                        return v___x_2229_;
                                                    }
                                                } else {
                                                    v___x_2230_ = l_Lean_Syntax_getArg(
                                                        v___x_2020_,
                                                        v___x_2019_,
                                                    );
                                                    v___x_2231_ =
                                                        l_Lean_Json_json_x2d____1___closed__3;
                                                    crate::leanh::lean_inc(v___x_2230_);
                                                    v___x_2232_ = l_Lean_Syntax_isOfKind(
                                                        v___x_2230_,
                                                        v___x_2231_,
                                                    );
                                                    if v___x_2232_ == 0 {
                                                        crate::leanh::lean_dec(v___x_2230_);
                                                        v___x_2233_ =
                                                            l_Lean_Syntax_isAntiquot(v___x_2020_);
                                                        if v___x_2233_ == 0 {
                                                            crate::leanh::lean_dec(v___x_2020_);
                                                            v___x_2234_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2014_);
                                                            return v___x_2234_;
                                                        } else {
                                                            v_quotContext_2235_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_a_2013_, 1,
                                                                );
                                                            v_currMacroScope_2236_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_a_2013_, 2,
                                                                );
                                                            v_ref_2237_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_a_2013_, 5,
                                                                );
                                                            v___x_2238_ =
                                                                l_Lean_Syntax_getAntiquotTerm(
                                                                    v___x_2020_,
                                                                );
                                                            crate::leanh::lean_dec(v___x_2020_);
                                                            v___x_2239_ = l_Lean_SourceInfo_fromRef(
                                                                v_ref_2237_,
                                                                v___x_2232_,
                                                            );
                                                            v___x_2240_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                            v___x_2241_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                                                            v___x_2242_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                                                            crate::leanh::lean_inc(
                                                                v_currMacroScope_2236_,
                                                            );
                                                            crate::leanh::lean_inc(
                                                                v_quotContext_2235_,
                                                            );
                                                            v___x_2243_ = l_Lean_addMacroScope(
                                                                v_quotContext_2235_,
                                                                v___x_2242_,
                                                                v_currMacroScope_2236_,
                                                            );
                                                            v___x_2244_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                                                            crate::leanh::lean_inc_n(
                                                                v___x_2239_,
                                                                2,
                                                            );
                                                            v___x_2245_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    3,
                                                                    4,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_2245_,
                                                                0,
                                                                v___x_2239_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_2245_,
                                                                1,
                                                                v___x_2241_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_2245_,
                                                                2,
                                                                v___x_2243_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_2245_,
                                                                3,
                                                                v___x_2244_,
                                                            );
                                                            v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                            v___x_2247_ = l_Lean_Syntax_node1(
                                                                v___x_2239_,
                                                                v___x_2246_,
                                                                v___x_2238_,
                                                            );
                                                            v___x_2248_ = l_Lean_Syntax_node2(
                                                                v___x_2239_,
                                                                v___x_2240_,
                                                                v___x_2245_,
                                                                v___x_2247_,
                                                            );
                                                            v___x_2249_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    0,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_2249_,
                                                                0,
                                                                v___x_2248_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_2249_,
                                                                1,
                                                                v_a_2014_,
                                                            );
                                                            return v___x_2249_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v_quotContext_2250_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 1,
                                                            );
                                                        v_currMacroScope_2251_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 2,
                                                            );
                                                        v_ref_2252_ = crate::leanh::lean_ctor_get(
                                                            v_a_2013_, 5,
                                                        );
                                                        v___x_2253_ = l_Lean_SourceInfo_fromRef(
                                                            v_ref_2252_,
                                                            v___x_2211_,
                                                        );
                                                        v___x_2254_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                        v___x_2255_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
                                                        v___x_2256_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34;
                                                        crate::leanh::lean_inc_n(
                                                            v_currMacroScope_2251_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_inc_n(
                                                            v_quotContext_2250_,
                                                            2,
                                                        );
                                                        v___x_2257_ = l_Lean_addMacroScope(
                                                            v_quotContext_2250_,
                                                            v___x_2256_,
                                                            v_currMacroScope_2251_,
                                                        );
                                                        v___x_2258_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38;
                                                        crate::leanh::lean_inc_n(v___x_2253_, 10);
                                                        v___x_2259_ = crate::leanh::lean_alloc_ctor(
                                                            3,
                                                            4,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2259_,
                                                            0,
                                                            v___x_2253_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2259_,
                                                            1,
                                                            v___x_2255_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2259_,
                                                            2,
                                                            v___x_2257_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2259_,
                                                            3,
                                                            v___x_2258_,
                                                        );
                                                        v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                        v___x_2261_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40;
                                                        v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4;
                                                        v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5;
                                                        v___x_2264_ = crate::leanh::lean_alloc_ctor(
                                                            2,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2264_,
                                                            0,
                                                            v___x_2253_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2264_,
                                                            1,
                                                            v___x_2263_,
                                                        );
                                                        v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7;
                                                        v___x_2266_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9);
                                                        v___x_2267_ = crate::leanh::lean_box(0);
                                                        v___x_2268_ = l_Lean_addMacroScope(
                                                            v_quotContext_2250_,
                                                            v___x_2267_,
                                                            v_currMacroScope_2251_,
                                                        );
                                                        v___x_2269_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41;
                                                        v___x_2270_ = crate::leanh::lean_alloc_ctor(
                                                            3,
                                                            4,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2270_,
                                                            0,
                                                            v___x_2253_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2270_,
                                                            1,
                                                            v___x_2266_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2270_,
                                                            2,
                                                            v___x_2268_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2270_,
                                                            3,
                                                            v___x_2269_,
                                                        );
                                                        v___x_2271_ = l_Lean_Syntax_node1(
                                                            v___x_2253_,
                                                            v___x_2265_,
                                                            v___x_2270_,
                                                        );
                                                        v___x_2272_ = l_Lean_Syntax_node2(
                                                            v___x_2253_,
                                                            v___x_2262_,
                                                            v___x_2264_,
                                                            v___x_2271_,
                                                        );
                                                        v___x_2273_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43;
                                                        v___x_2274_ =
                                                            l_Lean_Json_json_x2d___00__closed__4;
                                                        v___x_2275_ = crate::leanh::lean_alloc_ctor(
                                                            2,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2275_,
                                                            0,
                                                            v___x_2253_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2275_,
                                                            1,
                                                            v___x_2274_,
                                                        );
                                                        v___x_2276_ = l_Lean_Syntax_node2(
                                                            v___x_2253_,
                                                            v___x_2273_,
                                                            v___x_2275_,
                                                            v___x_2230_,
                                                        );
                                                        v___x_2277_ =
                                                            l_Lean_Json_json_quot___closed__13;
                                                        v___x_2278_ = crate::leanh::lean_alloc_ctor(
                                                            2,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2278_,
                                                            0,
                                                            v___x_2253_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2278_,
                                                            1,
                                                            v___x_2277_,
                                                        );
                                                        v___x_2279_ = l_Lean_Syntax_node3(
                                                            v___x_2253_,
                                                            v___x_2261_,
                                                            v___x_2272_,
                                                            v___x_2276_,
                                                            v___x_2278_,
                                                        );
                                                        v___x_2280_ = l_Lean_Syntax_node1(
                                                            v___x_2253_,
                                                            v___x_2260_,
                                                            v___x_2279_,
                                                        );
                                                        v___x_2281_ = l_Lean_Syntax_node2(
                                                            v___x_2253_,
                                                            v___x_2254_,
                                                            v___x_2259_,
                                                            v___x_2280_,
                                                        );
                                                        v___x_2282_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2282_,
                                                            0,
                                                            v___x_2281_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2282_,
                                                            1,
                                                            v_a_2014_,
                                                        );
                                                        return v___x_2282_;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v___x_2210_);
                                                v___x_2283_ =
                                                    l_Lean_Syntax_getArg(v___x_2020_, v___x_2019_);
                                                v___x_2284_ = l_Lean_Json_json_x2d____1___closed__3;
                                                crate::leanh::lean_inc(v___x_2283_);
                                                v___x_2285_ = l_Lean_Syntax_isOfKind(
                                                    v___x_2283_,
                                                    v___x_2284_,
                                                );
                                                if v___x_2285_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2283_);
                                                    v___x_2286_ =
                                                        l_Lean_Syntax_isAntiquot(v___x_2020_);
                                                    if v___x_2286_ == 0 {
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v___x_2287_ =
                                                            l_Lean_Macro_throwUnsupported___redArg(
                                                                v_a_2014_,
                                                            );
                                                        return v___x_2287_;
                                                    } else {
                                                        v_quotContext_2288_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 1,
                                                            );
                                                        v_currMacroScope_2289_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 2,
                                                            );
                                                        v_ref_2290_ = crate::leanh::lean_ctor_get(
                                                            v_a_2013_, 5,
                                                        );
                                                        v___x_2291_ = l_Lean_Syntax_getAntiquotTerm(
                                                            v___x_2020_,
                                                        );
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v___x_2292_ = l_Lean_SourceInfo_fromRef(
                                                            v_ref_2290_,
                                                            v___x_2285_,
                                                        );
                                                        v___x_2293_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                        v___x_2294_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                                                        v___x_2295_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                                                        crate::leanh::lean_inc(
                                                            v_currMacroScope_2289_,
                                                        );
                                                        crate::leanh::lean_inc(v_quotContext_2288_);
                                                        v___x_2296_ = l_Lean_addMacroScope(
                                                            v_quotContext_2288_,
                                                            v___x_2295_,
                                                            v_currMacroScope_2289_,
                                                        );
                                                        v___x_2297_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                                                        crate::leanh::lean_inc_n(v___x_2292_, 2);
                                                        v___x_2298_ = crate::leanh::lean_alloc_ctor(
                                                            3,
                                                            4,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2298_,
                                                            0,
                                                            v___x_2292_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2298_,
                                                            1,
                                                            v___x_2294_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2298_,
                                                            2,
                                                            v___x_2296_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2298_,
                                                            3,
                                                            v___x_2297_,
                                                        );
                                                        v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                        v___x_2300_ = l_Lean_Syntax_node1(
                                                            v___x_2292_,
                                                            v___x_2299_,
                                                            v___x_2291_,
                                                        );
                                                        v___x_2301_ = l_Lean_Syntax_node2(
                                                            v___x_2292_,
                                                            v___x_2293_,
                                                            v___x_2298_,
                                                            v___x_2300_,
                                                        );
                                                        v___x_2302_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2302_,
                                                            0,
                                                            v___x_2301_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2302_,
                                                            1,
                                                            v_a_2014_,
                                                        );
                                                        return v___x_2302_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v___x_2020_);
                                                    v_quotContext_2303_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 1);
                                                    v_currMacroScope_2304_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 2);
                                                    v_ref_2305_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 5);
                                                    v___x_2306_ = l_Lean_SourceInfo_fromRef(
                                                        v_ref_2305_,
                                                        v___x_2031_,
                                                    );
                                                    v___x_2307_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                    v___x_2308_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
                                                    v___x_2309_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34;
                                                    crate::leanh::lean_inc(v_currMacroScope_2304_);
                                                    crate::leanh::lean_inc(v_quotContext_2303_);
                                                    v___x_2310_ = l_Lean_addMacroScope(
                                                        v_quotContext_2303_,
                                                        v___x_2309_,
                                                        v_currMacroScope_2304_,
                                                    );
                                                    v___x_2311_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38;
                                                    crate::leanh::lean_inc_n(v___x_2306_, 2);
                                                    v___x_2312_ = crate::leanh::lean_alloc_ctor(
                                                        3,
                                                        4,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2312_,
                                                        0,
                                                        v___x_2306_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2312_,
                                                        1,
                                                        v___x_2308_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2312_,
                                                        2,
                                                        v___x_2310_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2312_,
                                                        3,
                                                        v___x_2311_,
                                                    );
                                                    v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                    v___x_2314_ = l_Lean_Syntax_node1(
                                                        v___x_2306_,
                                                        v___x_2313_,
                                                        v___x_2283_,
                                                    );
                                                    v___x_2315_ = l_Lean_Syntax_node2(
                                                        v___x_2306_,
                                                        v___x_2307_,
                                                        v___x_2312_,
                                                        v___x_2314_,
                                                    );
                                                    v___x_2316_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2316_,
                                                        0,
                                                        v___x_2315_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2316_,
                                                        1,
                                                        v_a_2014_,
                                                    );
                                                    return v___x_2316_;
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_2317_ =
                                            l_Lean_Syntax_getArg(v___x_2020_, v___x_2027_);
                                        crate::leanh::lean_inc(v___x_2317_);
                                        v___x_2318_ =
                                            l_Lean_Syntax_matchesNull(v___x_2317_, v___x_2027_);
                                        if v___x_2318_ == 0 {
                                            v___x_2319_ =
                                                l_Lean_Syntax_matchesNull(v___x_2317_, v___x_2019_);
                                            if v___x_2319_ == 0 {
                                                v___x_2320_ = l_Lean_Syntax_isAntiquot(v___x_2020_);
                                                if v___x_2320_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2020_);
                                                    v___x_2321_ =
                                                        l_Lean_Macro_throwUnsupported___redArg(
                                                            v_a_2014_,
                                                        );
                                                    return v___x_2321_;
                                                } else {
                                                    v_quotContext_2322_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 1);
                                                    v_currMacroScope_2323_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 2);
                                                    v_ref_2324_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 5);
                                                    v___x_2325_ =
                                                        l_Lean_Syntax_getAntiquotTerm(v___x_2020_);
                                                    crate::leanh::lean_dec(v___x_2020_);
                                                    v___x_2326_ = l_Lean_SourceInfo_fromRef(
                                                        v_ref_2324_,
                                                        v___x_2319_,
                                                    );
                                                    v___x_2327_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                    v___x_2328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                                                    v___x_2329_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                                                    crate::leanh::lean_inc(v_currMacroScope_2323_);
                                                    crate::leanh::lean_inc(v_quotContext_2322_);
                                                    v___x_2330_ = l_Lean_addMacroScope(
                                                        v_quotContext_2322_,
                                                        v___x_2329_,
                                                        v_currMacroScope_2323_,
                                                    );
                                                    v___x_2331_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                                                    crate::leanh::lean_inc_n(v___x_2326_, 2);
                                                    v___x_2332_ = crate::leanh::lean_alloc_ctor(
                                                        3,
                                                        4,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2332_,
                                                        0,
                                                        v___x_2326_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2332_,
                                                        1,
                                                        v___x_2328_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2332_,
                                                        2,
                                                        v___x_2330_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2332_,
                                                        3,
                                                        v___x_2331_,
                                                    );
                                                    v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                    v___x_2334_ = l_Lean_Syntax_node1(
                                                        v___x_2326_,
                                                        v___x_2333_,
                                                        v___x_2325_,
                                                    );
                                                    v___x_2335_ = l_Lean_Syntax_node2(
                                                        v___x_2326_,
                                                        v___x_2327_,
                                                        v___x_2332_,
                                                        v___x_2334_,
                                                    );
                                                    v___x_2336_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2336_,
                                                        0,
                                                        v___x_2335_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2336_,
                                                        1,
                                                        v_a_2014_,
                                                    );
                                                    return v___x_2336_;
                                                }
                                            } else {
                                                v___x_2337_ =
                                                    l_Lean_Syntax_getArg(v___x_2020_, v___x_2019_);
                                                v___x_2338_ = l_Lean_Json_json_x2d___00__closed__8;
                                                crate::leanh::lean_inc(v___x_2337_);
                                                v___x_2339_ = l_Lean_Syntax_isOfKind(
                                                    v___x_2337_,
                                                    v___x_2338_,
                                                );
                                                if v___x_2339_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2337_);
                                                    v___x_2340_ =
                                                        l_Lean_Syntax_isAntiquot(v___x_2020_);
                                                    if v___x_2340_ == 0 {
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v___x_2341_ =
                                                            l_Lean_Macro_throwUnsupported___redArg(
                                                                v_a_2014_,
                                                            );
                                                        return v___x_2341_;
                                                    } else {
                                                        v_quotContext_2342_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 1,
                                                            );
                                                        v_currMacroScope_2343_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_2013_, 2,
                                                            );
                                                        v_ref_2344_ = crate::leanh::lean_ctor_get(
                                                            v_a_2013_, 5,
                                                        );
                                                        v___x_2345_ = l_Lean_Syntax_getAntiquotTerm(
                                                            v___x_2020_,
                                                        );
                                                        crate::leanh::lean_dec(v___x_2020_);
                                                        v___x_2346_ = l_Lean_SourceInfo_fromRef(
                                                            v_ref_2344_,
                                                            v___x_2339_,
                                                        );
                                                        v___x_2347_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                        v___x_2348_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                                                        v___x_2349_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                                                        crate::leanh::lean_inc(
                                                            v_currMacroScope_2343_,
                                                        );
                                                        crate::leanh::lean_inc(v_quotContext_2342_);
                                                        v___x_2350_ = l_Lean_addMacroScope(
                                                            v_quotContext_2342_,
                                                            v___x_2349_,
                                                            v_currMacroScope_2343_,
                                                        );
                                                        v___x_2351_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                                                        crate::leanh::lean_inc_n(v___x_2346_, 2);
                                                        v___x_2352_ = crate::leanh::lean_alloc_ctor(
                                                            3,
                                                            4,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2352_,
                                                            0,
                                                            v___x_2346_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2352_,
                                                            1,
                                                            v___x_2348_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2352_,
                                                            2,
                                                            v___x_2350_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2352_,
                                                            3,
                                                            v___x_2351_,
                                                        );
                                                        v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                        v___x_2354_ = l_Lean_Syntax_node1(
                                                            v___x_2346_,
                                                            v___x_2353_,
                                                            v___x_2345_,
                                                        );
                                                        v___x_2355_ = l_Lean_Syntax_node2(
                                                            v___x_2346_,
                                                            v___x_2347_,
                                                            v___x_2352_,
                                                            v___x_2354_,
                                                        );
                                                        v___x_2356_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2356_,
                                                            0,
                                                            v___x_2355_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2356_,
                                                            1,
                                                            v_a_2014_,
                                                        );
                                                        return v___x_2356_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v___x_2020_);
                                                    v_quotContext_2357_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 1);
                                                    v_currMacroScope_2358_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 2);
                                                    v_ref_2359_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 5);
                                                    v___x_2360_ = l_Lean_SourceInfo_fromRef(
                                                        v_ref_2359_,
                                                        v___x_2318_,
                                                    );
                                                    v___x_2361_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                    v___x_2362_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
                                                    v___x_2363_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34;
                                                    crate::leanh::lean_inc_n(
                                                        v_currMacroScope_2358_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_inc_n(
                                                        v_quotContext_2357_,
                                                        2,
                                                    );
                                                    v___x_2364_ = l_Lean_addMacroScope(
                                                        v_quotContext_2357_,
                                                        v___x_2363_,
                                                        v_currMacroScope_2358_,
                                                    );
                                                    v___x_2365_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38;
                                                    crate::leanh::lean_inc_n(v___x_2360_, 10);
                                                    v___x_2366_ = crate::leanh::lean_alloc_ctor(
                                                        3,
                                                        4,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2366_,
                                                        0,
                                                        v___x_2360_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2366_,
                                                        1,
                                                        v___x_2362_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2366_,
                                                        2,
                                                        v___x_2364_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2366_,
                                                        3,
                                                        v___x_2365_,
                                                    );
                                                    v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                    v___x_2368_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__40;
                                                    v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__4;
                                                    v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__5;
                                                    v___x_2371_ = crate::leanh::lean_alloc_ctor(
                                                        2,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2371_,
                                                        0,
                                                        v___x_2360_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2371_,
                                                        1,
                                                        v___x_2370_,
                                                    );
                                                    v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__7;
                                                    v___x_2373_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__9);
                                                    v___x_2374_ = crate::leanh::lean_box(0);
                                                    v___x_2375_ = l_Lean_addMacroScope(
                                                        v_quotContext_2357_,
                                                        v___x_2374_,
                                                        v_currMacroScope_2358_,
                                                    );
                                                    v___x_2376_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__41;
                                                    v___x_2377_ = crate::leanh::lean_alloc_ctor(
                                                        3,
                                                        4,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2377_,
                                                        0,
                                                        v___x_2360_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2377_,
                                                        1,
                                                        v___x_2373_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2377_,
                                                        2,
                                                        v___x_2375_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2377_,
                                                        3,
                                                        v___x_2376_,
                                                    );
                                                    v___x_2378_ = l_Lean_Syntax_node1(
                                                        v___x_2360_,
                                                        v___x_2372_,
                                                        v___x_2377_,
                                                    );
                                                    v___x_2379_ = l_Lean_Syntax_node2(
                                                        v___x_2360_,
                                                        v___x_2369_,
                                                        v___x_2371_,
                                                        v___x_2378_,
                                                    );
                                                    v___x_2380_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__43;
                                                    v___x_2381_ =
                                                        l_Lean_Json_json_x2d___00__closed__4;
                                                    v___x_2382_ = crate::leanh::lean_alloc_ctor(
                                                        2,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2382_,
                                                        0,
                                                        v___x_2360_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2382_,
                                                        1,
                                                        v___x_2381_,
                                                    );
                                                    v___x_2383_ = l_Lean_Syntax_node2(
                                                        v___x_2360_,
                                                        v___x_2380_,
                                                        v___x_2382_,
                                                        v___x_2337_,
                                                    );
                                                    v___x_2384_ =
                                                        l_Lean_Json_json_quot___closed__13;
                                                    v___x_2385_ = crate::leanh::lean_alloc_ctor(
                                                        2,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2385_,
                                                        0,
                                                        v___x_2360_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2385_,
                                                        1,
                                                        v___x_2384_,
                                                    );
                                                    v___x_2386_ = l_Lean_Syntax_node3(
                                                        v___x_2360_,
                                                        v___x_2368_,
                                                        v___x_2379_,
                                                        v___x_2383_,
                                                        v___x_2385_,
                                                    );
                                                    v___x_2387_ = l_Lean_Syntax_node1(
                                                        v___x_2360_,
                                                        v___x_2367_,
                                                        v___x_2386_,
                                                    );
                                                    v___x_2388_ = l_Lean_Syntax_node2(
                                                        v___x_2360_,
                                                        v___x_2361_,
                                                        v___x_2366_,
                                                        v___x_2387_,
                                                    );
                                                    v___x_2389_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2389_,
                                                        0,
                                                        v___x_2388_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2389_,
                                                        1,
                                                        v_a_2014_,
                                                    );
                                                    return v___x_2389_;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v___x_2317_);
                                            v___x_2390_ =
                                                l_Lean_Syntax_getArg(v___x_2020_, v___x_2019_);
                                            v___x_2391_ = l_Lean_Json_json_x2d___00__closed__8;
                                            crate::leanh::lean_inc(v___x_2390_);
                                            v___x_2392_ =
                                                l_Lean_Syntax_isOfKind(v___x_2390_, v___x_2391_);
                                            if v___x_2392_ == 0 {
                                                crate::leanh::lean_dec(v___x_2390_);
                                                v___x_2393_ = l_Lean_Syntax_isAntiquot(v___x_2020_);
                                                if v___x_2393_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2020_);
                                                    v___x_2394_ =
                                                        l_Lean_Macro_throwUnsupported___redArg(
                                                            v_a_2014_,
                                                        );
                                                    return v___x_2394_;
                                                } else {
                                                    v_quotContext_2395_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 1);
                                                    v_currMacroScope_2396_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 2);
                                                    v_ref_2397_ =
                                                        crate::leanh::lean_ctor_get(v_a_2013_, 5);
                                                    v___x_2398_ =
                                                        l_Lean_Syntax_getAntiquotTerm(v___x_2020_);
                                                    crate::leanh::lean_dec(v___x_2020_);
                                                    v___x_2399_ = l_Lean_SourceInfo_fromRef(
                                                        v_ref_2397_,
                                                        v___x_2392_,
                                                    );
                                                    v___x_2400_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                    v___x_2401_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                                                    v___x_2402_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                                                    crate::leanh::lean_inc(v_currMacroScope_2396_);
                                                    crate::leanh::lean_inc(v_quotContext_2395_);
                                                    v___x_2403_ = l_Lean_addMacroScope(
                                                        v_quotContext_2395_,
                                                        v___x_2402_,
                                                        v_currMacroScope_2396_,
                                                    );
                                                    v___x_2404_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                                                    crate::leanh::lean_inc_n(v___x_2399_, 2);
                                                    v___x_2405_ = crate::leanh::lean_alloc_ctor(
                                                        3,
                                                        4,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2405_,
                                                        0,
                                                        v___x_2399_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2405_,
                                                        1,
                                                        v___x_2401_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2405_,
                                                        2,
                                                        v___x_2403_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2405_,
                                                        3,
                                                        v___x_2404_,
                                                    );
                                                    v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                    v___x_2407_ = l_Lean_Syntax_node1(
                                                        v___x_2399_,
                                                        v___x_2406_,
                                                        v___x_2398_,
                                                    );
                                                    v___x_2408_ = l_Lean_Syntax_node2(
                                                        v___x_2399_,
                                                        v___x_2400_,
                                                        v___x_2405_,
                                                        v___x_2407_,
                                                    );
                                                    v___x_2409_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2409_,
                                                        0,
                                                        v___x_2408_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2409_,
                                                        1,
                                                        v_a_2014_,
                                                    );
                                                    return v___x_2409_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v___x_2020_);
                                                v_quotContext_2410_ =
                                                    crate::leanh::lean_ctor_get(v_a_2013_, 1);
                                                v_currMacroScope_2411_ =
                                                    crate::leanh::lean_ctor_get(v_a_2013_, 2);
                                                v_ref_2412_ =
                                                    crate::leanh::lean_ctor_get(v_a_2013_, 5);
                                                v___x_2413_ = l_Lean_SourceInfo_fromRef(
                                                    v_ref_2412_,
                                                    v___x_2029_,
                                                );
                                                v___x_2414_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                                v___x_2415_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__33);
                                                v___x_2416_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__34;
                                                crate::leanh::lean_inc(v_currMacroScope_2411_);
                                                crate::leanh::lean_inc(v_quotContext_2410_);
                                                v___x_2417_ = l_Lean_addMacroScope(
                                                    v_quotContext_2410_,
                                                    v___x_2416_,
                                                    v_currMacroScope_2411_,
                                                );
                                                v___x_2418_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__38;
                                                crate::leanh::lean_inc_n(v___x_2413_, 2);
                                                v___x_2419_ =
                                                    crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2419_,
                                                    0,
                                                    v___x_2413_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2419_,
                                                    1,
                                                    v___x_2415_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2419_,
                                                    2,
                                                    v___x_2417_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2419_,
                                                    3,
                                                    v___x_2418_,
                                                );
                                                v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                                v___x_2421_ = l_Lean_Syntax_node1(
                                                    v___x_2413_,
                                                    v___x_2420_,
                                                    v___x_2390_,
                                                );
                                                v___x_2422_ = l_Lean_Syntax_node2(
                                                    v___x_2413_,
                                                    v___x_2414_,
                                                    v___x_2419_,
                                                    v___x_2421_,
                                                );
                                                v___x_2423_ =
                                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2423_,
                                                    0,
                                                    v___x_2422_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2423_,
                                                    1,
                                                    v_a_2014_,
                                                );
                                                return v___x_2423_;
                                            }
                                        }
                                    }
                                } else {
                                    v___x_2424_ = l_Lean_Syntax_getArg(v___x_2020_, v___x_2027_);
                                    v___x_2425_ = l_Lean_Json_json___00__closed__3;
                                    crate::leanh::lean_inc(v___x_2424_);
                                    v___x_2426_ = l_Lean_Syntax_isOfKind(v___x_2424_, v___x_2425_);
                                    if v___x_2426_ == 0 {
                                        crate::leanh::lean_dec(v___x_2424_);
                                        v___x_2427_ = l_Lean_Syntax_isAntiquot(v___x_2020_);
                                        if v___x_2427_ == 0 {
                                            crate::leanh::lean_dec(v___x_2020_);
                                            v___x_2428_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v_a_2014_);
                                            return v___x_2428_;
                                        } else {
                                            v_quotContext_2429_ =
                                                crate::leanh::lean_ctor_get(v_a_2013_, 1);
                                            v_currMacroScope_2430_ =
                                                crate::leanh::lean_ctor_get(v_a_2013_, 2);
                                            v_ref_2431_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                                            v___x_2432_ =
                                                l_Lean_Syntax_getAntiquotTerm(v___x_2020_);
                                            crate::leanh::lean_dec(v___x_2020_);
                                            v___x_2433_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_2431_, v___x_2426_);
                                            v___x_2434_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                            v___x_2435_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                                            v___x_2436_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                                            crate::leanh::lean_inc(v_currMacroScope_2430_);
                                            crate::leanh::lean_inc(v_quotContext_2429_);
                                            v___x_2437_ = l_Lean_addMacroScope(
                                                v_quotContext_2429_,
                                                v___x_2436_,
                                                v_currMacroScope_2430_,
                                            );
                                            v___x_2438_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                                            crate::leanh::lean_inc_n(v___x_2433_, 2);
                                            v___x_2439_ =
                                                crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2439_,
                                                0,
                                                v___x_2433_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2439_,
                                                1,
                                                v___x_2435_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2439_,
                                                2,
                                                v___x_2437_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2439_,
                                                3,
                                                v___x_2438_,
                                            );
                                            v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                            v___x_2441_ = l_Lean_Syntax_node1(
                                                v___x_2433_,
                                                v___x_2440_,
                                                v___x_2432_,
                                            );
                                            v___x_2442_ = l_Lean_Syntax_node2(
                                                v___x_2433_,
                                                v___x_2434_,
                                                v___x_2439_,
                                                v___x_2441_,
                                            );
                                            v___x_2443_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2443_,
                                                0,
                                                v___x_2442_,
                                            );
                                            crate::leanh::lean_ctor_set(v___x_2443_, 1, v_a_2014_);
                                            return v___x_2443_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2020_);
                                        v_quotContext_2444_ =
                                            crate::leanh::lean_ctor_get(v_a_2013_, 1);
                                        v_currMacroScope_2445_ =
                                            crate::leanh::lean_ctor_get(v_a_2013_, 2);
                                        v_ref_2446_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                                        v___x_2447_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_2446_, v___x_2026_);
                                        v___x_2448_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                        v___x_2449_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__45);
                                        v___x_2450_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__46;
                                        crate::leanh::lean_inc(v_currMacroScope_2445_);
                                        crate::leanh::lean_inc(v_quotContext_2444_);
                                        v___x_2451_ = l_Lean_addMacroScope(
                                            v_quotContext_2444_,
                                            v___x_2450_,
                                            v_currMacroScope_2445_,
                                        );
                                        v___x_2452_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__50;
                                        crate::leanh::lean_inc_n(v___x_2447_, 2);
                                        v___x_2453_ =
                                            crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2453_, 0, v___x_2447_);
                                        crate::leanh::lean_ctor_set(v___x_2453_, 1, v___x_2449_);
                                        crate::leanh::lean_ctor_set(v___x_2453_, 2, v___x_2451_);
                                        crate::leanh::lean_ctor_set(v___x_2453_, 3, v___x_2452_);
                                        v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                        v___x_2455_ = l_Lean_Syntax_node1(
                                            v___x_2447_,
                                            v___x_2454_,
                                            v___x_2424_,
                                        );
                                        v___x_2456_ = l_Lean_Syntax_node2(
                                            v___x_2447_,
                                            v___x_2448_,
                                            v___x_2453_,
                                            v___x_2455_,
                                        );
                                        v___x_2457_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2457_, 0, v___x_2456_);
                                        crate::leanh::lean_ctor_set(v___x_2457_, 1, v_a_2014_);
                                        return v___x_2457_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2020_);
                                v_quotContext_2458_ = crate::leanh::lean_ctor_get(v_a_2013_, 1);
                                v_currMacroScope_2459_ = crate::leanh::lean_ctor_get(v_a_2013_, 2);
                                v_ref_2460_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                                v___x_2461_ = l_Lean_SourceInfo_fromRef(v_ref_2460_, v___x_2024_);
                                v___x_2462_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                                v___x_2463_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
                                v___x_2464_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54;
                                crate::leanh::lean_inc_n(v_currMacroScope_2459_, 2);
                                crate::leanh::lean_inc_n(v_quotContext_2458_, 2);
                                v___x_2465_ = l_Lean_addMacroScope(
                                    v_quotContext_2458_,
                                    v___x_2464_,
                                    v_currMacroScope_2459_,
                                );
                                v___x_2466_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58;
                                crate::leanh::lean_inc_n(v___x_2461_, 3);
                                v___x_2467_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2467_, 0, v___x_2461_);
                                crate::leanh::lean_ctor_set(v___x_2467_, 1, v___x_2463_);
                                crate::leanh::lean_ctor_set(v___x_2467_, 2, v___x_2465_);
                                crate::leanh::lean_ctor_set(v___x_2467_, 3, v___x_2466_);
                                v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                                v___x_2469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__60);
                                v___x_2470_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__62;
                                v___x_2471_ = l_Lean_addMacroScope(
                                    v_quotContext_2458_,
                                    v___x_2470_,
                                    v_currMacroScope_2459_,
                                );
                                v___x_2472_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__66;
                                v___x_2473_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2473_, 0, v___x_2461_);
                                crate::leanh::lean_ctor_set(v___x_2473_, 1, v___x_2469_);
                                crate::leanh::lean_ctor_set(v___x_2473_, 2, v___x_2471_);
                                crate::leanh::lean_ctor_set(v___x_2473_, 3, v___x_2472_);
                                v___x_2474_ =
                                    l_Lean_Syntax_node1(v___x_2461_, v___x_2468_, v___x_2473_);
                                v___x_2475_ = l_Lean_Syntax_node2(
                                    v___x_2461_,
                                    v___x_2462_,
                                    v___x_2467_,
                                    v___x_2474_,
                                );
                                v___x_2476_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2476_, 0, v___x_2475_);
                                crate::leanh::lean_ctor_set(v___x_2476_, 1, v_a_2014_);
                                return v___x_2476_;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2020_);
                            v_quotContext_2477_ = crate::leanh::lean_ctor_get(v_a_2013_, 1);
                            v_currMacroScope_2478_ = crate::leanh::lean_ctor_get(v_a_2013_, 2);
                            v_ref_2479_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                            v___x_2480_ = l_Lean_SourceInfo_fromRef(v_ref_2479_, v___x_2022_);
                            v___x_2481_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                            v___x_2482_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__52);
                            v___x_2483_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__54;
                            crate::leanh::lean_inc_n(v_currMacroScope_2478_, 2);
                            crate::leanh::lean_inc_n(v_quotContext_2477_, 2);
                            v___x_2484_ = l_Lean_addMacroScope(
                                v_quotContext_2477_,
                                v___x_2483_,
                                v_currMacroScope_2478_,
                            );
                            v___x_2485_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__58;
                            crate::leanh::lean_inc_n(v___x_2480_, 3);
                            v___x_2486_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2486_, 0, v___x_2480_);
                            crate::leanh::lean_ctor_set(v___x_2486_, 1, v___x_2482_);
                            crate::leanh::lean_ctor_set(v___x_2486_, 2, v___x_2484_);
                            crate::leanh::lean_ctor_set(v___x_2486_, 3, v___x_2485_);
                            v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                            v___x_2488_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__68);
                            v___x_2489_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__69;
                            v___x_2490_ = l_Lean_addMacroScope(
                                v_quotContext_2477_,
                                v___x_2489_,
                                v_currMacroScope_2478_,
                            );
                            v___x_2491_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__73;
                            v___x_2492_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2492_, 0, v___x_2480_);
                            crate::leanh::lean_ctor_set(v___x_2492_, 1, v___x_2488_);
                            crate::leanh::lean_ctor_set(v___x_2492_, 2, v___x_2490_);
                            crate::leanh::lean_ctor_set(v___x_2492_, 3, v___x_2491_);
                            v___x_2493_ =
                                l_Lean_Syntax_node1(v___x_2480_, v___x_2487_, v___x_2492_);
                            v___x_2494_ = l_Lean_Syntax_node2(
                                v___x_2480_,
                                v___x_2481_,
                                v___x_2486_,
                                v___x_2493_,
                            );
                            v___x_2495_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2495_, 0, v___x_2494_);
                            crate::leanh::lean_ctor_set(v___x_2495_, 1, v_a_2014_);
                            return v___x_2495_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2020_);
                        v_quotContext_2496_ = crate::leanh::lean_ctor_get(v_a_2013_, 1);
                        v_currMacroScope_2497_ = crate::leanh::lean_ctor_get(v_a_2013_, 2);
                        v_ref_2498_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                        v___x_2499_ = 0;
                        v___x_2500_ = l_Lean_SourceInfo_fromRef(v_ref_2498_, v___x_2499_);
                        v___x_2501_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__75);
                        v___x_2502_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__76;
                        crate::leanh::lean_inc(v_currMacroScope_2497_);
                        crate::leanh::lean_inc(v_quotContext_2496_);
                        v___x_2503_ = l_Lean_addMacroScope(
                            v_quotContext_2496_,
                            v___x_2502_,
                            v_currMacroScope_2497_,
                        );
                        v___x_2504_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__80;
                        v___x_2505_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2505_, 0, v___x_2500_);
                        crate::leanh::lean_ctor_set(v___x_2505_, 1, v___x_2501_);
                        crate::leanh::lean_ctor_set(v___x_2505_, 2, v___x_2503_);
                        crate::leanh::lean_ctor_set(v___x_2505_, 3, v___x_2504_);
                        v___x_2506_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2506_, 0, v___x_2505_);
                        crate::leanh::lean_ctor_set(v___x_2506_, 1, v_a_2014_);
                        return v___x_2506_;
                    }
                }
            }
            1 => {
                v_sz_2036_ = lean_array_size(v___y_2035_);
                v___x_2037_ = 0usize;
                v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__6(v_sz_2036_, v___x_2037_, v___y_2035_);
                if crate::leanh::lean_obj_tag(v___x_2038_) == 0 {
                    v___x_2039_ = l_Lean_Syntax_isAntiquot(v___x_2020_);
                    if v___x_2039_ == 0 {
                        crate::leanh::lean_dec(v___x_2020_);
                        v___x_2040_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2014_);
                        return v___x_2040_;
                    } else {
                        v_quotContext_2041_ = crate::leanh::lean_ctor_get(v_a_2013_, 1);
                        v_currMacroScope_2042_ = crate::leanh::lean_ctor_get(v_a_2013_, 2);
                        v_ref_2043_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                        v___x_2044_ = l_Lean_Syntax_getAntiquotTerm(v___x_2020_);
                        crate::leanh::lean_dec(v___x_2020_);
                        v___x_2045_ = l_Lean_SourceInfo_fromRef(v_ref_2043_, v___x_2033_);
                        v___x_2046_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                        v___x_2047_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                        v___x_2048_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                        crate::leanh::lean_inc(v_currMacroScope_2042_);
                        crate::leanh::lean_inc(v_quotContext_2041_);
                        v___x_2049_ = l_Lean_addMacroScope(
                            v_quotContext_2041_,
                            v___x_2048_,
                            v_currMacroScope_2042_,
                        );
                        v___x_2050_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                        crate::leanh::lean_inc_n(v___x_2045_, 2);
                        v___x_2051_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2051_, 0, v___x_2045_);
                        crate::leanh::lean_ctor_set(v___x_2051_, 1, v___x_2047_);
                        crate::leanh::lean_ctor_set(v___x_2051_, 2, v___x_2049_);
                        crate::leanh::lean_ctor_set(v___x_2051_, 3, v___x_2050_);
                        v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                        v___x_2053_ = l_Lean_Syntax_node1(v___x_2045_, v___x_2052_, v___x_2044_);
                        v___x_2054_ =
                            l_Lean_Syntax_node2(v___x_2045_, v___x_2046_, v___x_2051_, v___x_2053_);
                        v___x_2055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_2054_);
                        crate::leanh::lean_ctor_set(v___x_2055_, 1, v_a_2014_);
                        return v___x_2055_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2020_);
                    v_val_2056_ = crate::leanh::lean_ctor_get(v___x_2038_, 0);
                    crate::leanh::lean_inc(v_val_2056_);
                    crate::leanh::lean_dec_ref_known(v___x_2038_, 1);
                    v_quotContext_2057_ = crate::leanh::lean_ctor_get(v_a_2013_, 1);
                    v_currMacroScope_2058_ = crate::leanh::lean_ctor_get(v_a_2013_, 2);
                    v_ref_2059_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                    v___x_2060_ = l_Lean_SourceInfo_fromRef(v_ref_2059_, v___x_2033_);
                    v___x_2061_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                    v___x_2062_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__11);
                    v___x_2063_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__13;
                    crate::leanh::lean_inc(v_currMacroScope_2058_);
                    crate::leanh::lean_inc(v_quotContext_2057_);
                    v___x_2064_ = l_Lean_addMacroScope(
                        v_quotContext_2057_,
                        v___x_2063_,
                        v_currMacroScope_2058_,
                    );
                    v___x_2065_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__17;
                    crate::leanh::lean_inc_n(v___x_2060_, 7);
                    v___x_2066_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2066_, 0, v___x_2060_);
                    crate::leanh::lean_ctor_set(v___x_2066_, 1, v___x_2062_);
                    crate::leanh::lean_ctor_set(v___x_2066_, 2, v___x_2064_);
                    crate::leanh::lean_ctor_set(v___x_2066_, 3, v___x_2065_);
                    v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                    v___x_2068_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__19;
                    v___x_2069_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__20;
                    v___x_2070_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2070_, 0, v___x_2060_);
                    crate::leanh::lean_ctor_set(v___x_2070_, 1, v___x_2069_);
                    v___x_2071_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
                    v_sz_2072_ = lean_array_size(v_val_2056_);
                    v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__7(v___x_2060_, v_sz_2072_, v___x_2037_, v_val_2056_);
                    v___x_2074_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22);
                    v___x_2075_ = l_Lean_mkSepArray(v___x_2073_, v___x_2074_);
                    crate::leanh::lean_dec_ref(v___x_2073_);
                    v___x_2076_ = l_Array_append___redArg(v___x_2071_, v___x_2075_);
                    crate::leanh::lean_dec_ref(v___x_2075_);
                    v___x_2077_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2077_, 0, v___x_2060_);
                    crate::leanh::lean_ctor_set(v___x_2077_, 1, v___x_2067_);
                    crate::leanh::lean_ctor_set(v___x_2077_, 2, v___x_2076_);
                    v___x_2078_ = l_Lean_Json_json_x5b___x5d___closed__9;
                    v___x_2079_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2060_);
                    crate::leanh::lean_ctor_set(v___x_2079_, 1, v___x_2078_);
                    v___x_2080_ = l_Lean_Syntax_node3(
                        v___x_2060_,
                        v___x_2068_,
                        v___x_2070_,
                        v___x_2077_,
                        v___x_2079_,
                    );
                    v___x_2081_ = l_Lean_Syntax_node1(v___x_2060_, v___x_2067_, v___x_2080_);
                    v___x_2082_ =
                        l_Lean_Syntax_node2(v___x_2060_, v___x_2061_, v___x_2066_, v___x_2081_);
                    v___x_2083_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2083_, 0, v___x_2082_);
                    crate::leanh::lean_ctor_set(v___x_2083_, 1, v_a_2014_);
                    return v___x_2083_;
                }
            }
            2 => {
                v_sz_2088_ = lean_array_size(v___y_2087_);
                v___x_2089_ = 0usize;
                v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__0(v_sz_2088_, v___x_2089_, v___y_2087_);
                if crate::leanh::lean_obj_tag(v___x_2090_) == 0 {
                    v___x_2091_ = l_Lean_Syntax_isAntiquot(v___x_2020_);
                    if v___x_2091_ == 0 {
                        crate::leanh::lean_dec(v___x_2020_);
                        v___x_2092_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2014_);
                        return v___x_2092_;
                    } else {
                        v_quotContext_2093_ = crate::leanh::lean_ctor_get(v_a_2013_, 1);
                        v_currMacroScope_2094_ = crate::leanh::lean_ctor_get(v_a_2013_, 2);
                        v_ref_2095_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                        v___x_2096_ = l_Lean_Syntax_getAntiquotTerm(v___x_2020_);
                        crate::leanh::lean_dec(v___x_2020_);
                        v___x_2097_ = l_Lean_SourceInfo_fromRef(v_ref_2095_, v___x_2085_);
                        v___x_2098_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                        v___x_2099_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__3);
                        v___x_2100_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__5;
                        crate::leanh::lean_inc(v_currMacroScope_2094_);
                        crate::leanh::lean_inc(v_quotContext_2093_);
                        v___x_2101_ = l_Lean_addMacroScope(
                            v_quotContext_2093_,
                            v___x_2100_,
                            v_currMacroScope_2094_,
                        );
                        v___x_2102_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__9;
                        crate::leanh::lean_inc_n(v___x_2097_, 2);
                        v___x_2103_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2103_, 0, v___x_2097_);
                        crate::leanh::lean_ctor_set(v___x_2103_, 1, v___x_2099_);
                        crate::leanh::lean_ctor_set(v___x_2103_, 2, v___x_2101_);
                        crate::leanh::lean_ctor_set(v___x_2103_, 3, v___x_2102_);
                        v___x_2104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                        v___x_2105_ = l_Lean_Syntax_node1(v___x_2097_, v___x_2104_, v___x_2096_);
                        v___x_2106_ =
                            l_Lean_Syntax_node2(v___x_2097_, v___x_2098_, v___x_2103_, v___x_2105_);
                        v___x_2107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2107_, 0, v___x_2106_);
                        crate::leanh::lean_ctor_set(v___x_2107_, 1, v_a_2014_);
                        return v___x_2107_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2020_);
                    v_val_2108_ = crate::leanh::lean_ctor_get(v___x_2090_, 0);
                    crate::leanh::lean_inc_n(v_val_2108_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2090_, 1);
                    v_sz_2109_ = lean_array_size(v_val_2108_);
                    v_vs_2110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__1(v_sz_2109_, v___x_2089_, v_val_2108_);
                    v_ks_2111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__2(v_sz_2109_, v___x_2089_, v_val_2108_);
                    v_sz_2112_ = lean_array_size(v_ks_2111_);
                    v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(v_sz_2112_, v___x_2089_, v_ks_2111_, v_a_2014_);
                    if crate::leanh::lean_obj_tag(v___x_2113_) == 0 {
                        v_a_2114_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                        v_a_2115_ = crate::leanh::lean_ctor_get(v___x_2113_, 1);
                        v_isSharedCheck_2149_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2113_)) as u8;
                        if v_isSharedCheck_2149_ == 0 {
                            v___x_2117_ = v___x_2113_;
                            v_isShared_2118_ = v_isSharedCheck_2149_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2115_);
                            crate::leanh::lean_inc(v_a_2114_);
                            crate::leanh::lean_dec(v___x_2113_);
                            v___x_2117_ = crate::leanh::lean_box(0);
                            v_isShared_2118_ = v_isSharedCheck_2149_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_vs_2110_);
                        v_a_2150_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                        v_a_2151_ = crate::leanh::lean_ctor_get(v___x_2113_, 1);
                        v_isSharedCheck_2158_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2113_)) as u8;
                        if v_isSharedCheck_2158_ == 0 {
                            v___x_2153_ = v___x_2113_;
                            v_isShared_2154_ = v_isSharedCheck_2158_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2151_);
                            crate::leanh::lean_inc(v_a_2150_);
                            crate::leanh::lean_dec(v___x_2113_);
                            v___x_2153_ = crate::leanh::lean_box(0);
                            v_isShared_2154_ = v_isSharedCheck_2158_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_quotContext_2119_ = crate::leanh::lean_ctor_get(v_a_2013_, 1);
                v_currMacroScope_2120_ = crate::leanh::lean_ctor_get(v_a_2013_, 2);
                v_ref_2121_ = crate::leanh::lean_ctor_get(v_a_2013_, 5);
                v___x_2122_ = l_Lean_SourceInfo_fromRef(v_ref_2121_, v___x_2085_);
                v___x_2123_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__1;
                v___x_2124_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__24);
                v___x_2125_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__26;
                crate::leanh::lean_inc_n(v_currMacroScope_2120_, 2);
                crate::leanh::lean_inc_n(v_quotContext_2119_, 2);
                v___x_2126_ =
                    l_Lean_addMacroScope(v_quotContext_2119_, v___x_2125_, v_currMacroScope_2120_);
                v___x_2127_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__28;
                crate::leanh::lean_inc_n(v___x_2122_, 7);
                v___x_2128_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2128_, 0, v___x_2122_);
                crate::leanh::lean_ctor_set(v___x_2128_, 1, v___x_2124_);
                crate::leanh::lean_ctor_set(v___x_2128_, 2, v___x_2126_);
                crate::leanh::lean_ctor_set(v___x_2128_, 3, v___x_2127_);
                v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4___closed__0;
                v___x_2130_ = l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__30;
                v___x_2131_ = l_Lean_Json_json_x5b___x5d___closed__2;
                v___x_2132_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2122_);
                crate::leanh::lean_ctor_set(v___x_2132_, 1, v___x_2131_);
                v___x_2133_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__21);
                v___x_2134_ = l_Array_zip___redArg(v_a_2114_, v_vs_2110_);
                crate::leanh::lean_dec_ref(v_vs_2110_);
                crate::leanh::lean_dec(v_a_2114_);
                v_sz_2135_ = lean_array_size(v___x_2134_);
                v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__4(v___x_2122_, v_quotContext_2119_, v_currMacroScope_2120_, v_sz_2135_, v___x_2089_, v___x_2134_);
                v___x_2137_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22), core::ptr::addr_of_mut!(l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22_once), _init_l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___closed__22);
                v___x_2138_ = l_Lean_mkSepArray(v___x_2136_, v___x_2137_);
                crate::leanh::lean_dec_ref(v___x_2136_);
                v___x_2139_ = l_Array_append___redArg(v___x_2133_, v___x_2138_);
                crate::leanh::lean_dec_ref(v___x_2138_);
                v___x_2140_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2140_, 0, v___x_2122_);
                crate::leanh::lean_ctor_set(v___x_2140_, 1, v___x_2129_);
                crate::leanh::lean_ctor_set(v___x_2140_, 2, v___x_2139_);
                v___x_2141_ = l_Lean_Json_json_x5b___x5d___closed__9;
                v___x_2142_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2122_);
                crate::leanh::lean_ctor_set(v___x_2142_, 1, v___x_2141_);
                v___x_2143_ = l_Lean_Syntax_node3(
                    v___x_2122_,
                    v___x_2130_,
                    v___x_2132_,
                    v___x_2140_,
                    v___x_2142_,
                );
                v___x_2144_ = l_Lean_Syntax_node1(v___x_2122_, v___x_2129_, v___x_2143_);
                v___x_2145_ =
                    l_Lean_Syntax_node2(v___x_2122_, v___x_2123_, v___x_2128_, v___x_2144_);
                if v_isShared_2118_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2117_, 0, v___x_2145_);
                    v___x_2147_ = v___x_2117_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_a_2115_);
                    v___x_2147_ = v_reuseFailAlloc_2148_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2147_;
            }
            5 => {
                if v_isShared_2154_ == 0 {
                    v___x_2156_ = v___x_2153_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2157_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_a_2151_);
                    v___x_2156_ = v_reuseFailAlloc_2157_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2156_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1___boxed(
    mut v_x_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2510_ =
        l_Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1(
            v_x_2507_, v_a_2508_, v_a_2509_,
        );
    crate::leanh::lean_dec_ref(v_a_2508_);
    return v_res_2510_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(
    mut v_sz_2511_: usize,
    mut v_i_2512_: usize,
    mut v_bs_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___redArg(v_sz_2511_, v_i_2512_, v_bs_2513_, v___y_2515_);
    return v___x_2516_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3___boxed(
    mut v_sz_2517_: *mut crate::leanh::LeanObject,
    mut v_i_2518_: *mut crate::leanh::LeanObject,
    mut v_bs_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2522_: usize = 0;
    let mut v_i_boxed_2523_: usize = 0;
    let mut v_res_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2522_ = crate::leanh::lean_unbox_usize(v_sz_2517_);
    crate::leanh::lean_dec(v_sz_2517_);
    v_i_boxed_2523_ = crate::leanh::lean_unbox_usize(v_i_2518_);
    crate::leanh::lean_dec(v_i_2518_);
    v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json___aux__Lean__Data__Json__Elab______macroRules__Lean__Json__termJson_x25____1_spec__3(v_sz_boxed_2522_, v_i_boxed_2523_, v_bs_2519_, v___y_2520_, v___y_2521_);
    crate::leanh::lean_dec_ref(v___y_2520_);
    return v_res_2524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_Elab(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_FromToJson(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_Elab(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Category_json = _init_l_Lean_Parser_Category_json();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Category_json);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json_Elab(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_FromToJson(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Elab(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_Elab(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Json_Elab(builtin);
}
