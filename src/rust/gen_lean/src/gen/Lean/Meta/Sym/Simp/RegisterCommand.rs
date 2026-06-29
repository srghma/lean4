// Lean compiler output
// Module: Lean.Meta.Sym.Simp.RegisterCommand
// Imports: Lean.Meta.Sym.Simp.Attr Lean.Meta.Sym.Simp.Variant Init.Data.ToString.Name Init.Data.String.Extra
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::String::Extra::{
    initialize_Init_Data_String_Extra, l_String_removeLeadingSpaces,
    runtime_initialize_Init_Data_String_Extra,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_toString,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_Syntax_mkStrLit, l_Lean_TSyntax_getDocString, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom,
    l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node7, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Attr::{
    initialize_Lean_Meta_Sym_Simp_Attr, runtime_initialize_Lean_Meta_Sym_Simp_Attr,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Variant::{
    initialize_Lean_Meta_Sym_Simp_Variant, runtime_initialize_Lean_Meta_Sym_Simp_Variant,
};
use crate::ffi::{
    lean_string_append, lean_string_intercalate,
};
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value:
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
    m_data: [83, 121, 109, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value)
            as *mut crate::leanh::LeanObject,
        4034176598647545331 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value:
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
    m_data: [83, 105, 109, 112, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value)
            as *mut crate::leanh::LeanObject,
        13806531830123099675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__8_value:
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
    m_data: [95, 114, 111, 111, 116, 95, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__8_value)
            as *mut crate::leanh::LeanObject,
        374889451593361368 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6987750457640845137 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value)
            as *mut crate::leanh::LeanObject,
        12535227884159716684 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value)
            as *mut crate::leanh::LeanObject,
        16576297762913773305 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 83, 121, 109, 83, 105, 109, 112, 65, 116, 116, 114,
        0,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__14_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value)
            as *mut crate::leanh::LeanObject,
        7783173021387648857 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__17_value:
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
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__17_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__19_value:
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
    m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__19_value)
            as *mut crate::leanh::LeanObject,
        18170484695678750185 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__21_value:
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
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__22_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__21_value)
            as *mut crate::leanh::LeanObject,
        3961966953292576997 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__23_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__22_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__24_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__20_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__23_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__25_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 95, 115, 121, 109, 95, 115, 105, 109, 112, 95, 97,
        116, 116, 114, 0,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__26_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__25_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__27_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__18_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__24_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__26_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__28_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__29_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__28_value)
            as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__30_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__29_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__31_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__18_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__27_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__30_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_registerSymSimpAttr___closed__32_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__16_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__31_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerSymSimpAttr___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Command_registerSymSimpAttr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 121, 110, 116, 97, 120, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0_value) as *mut crate::leanh::LeanObject,2812521669163367463 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__3_value) as *mut crate::leanh::LeanObject,17682753938374962505 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__7_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__8_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__9_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 111, 109, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__9_value) as *mut crate::leanh::LeanObject,1765827125244227832 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__10_value) as *mut crate::leanh::LeanObject,6376237424612349584 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 116, 114, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12_value) as *mut crate::leanh::LeanObject,6289677862665402693 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15_value) as *mut crate::leanh::LeanObject,10411423847645546083 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17_value) as *mut crate::leanh::LeanObject,4787239732180154236 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__19_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 75, 101, 121, 119, 111, 114, 100, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__19_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__19_value) as *mut crate::leanh::LeanObject,387456110215466097 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 120, 116, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21_value) as *mut crate::leanh::LeanObject,6455343056875556081 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__25_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__25_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__25_value) as *mut crate::leanh::LeanObject,4498178684837002829 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__27_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 121, 109, 83, 105, 109, 112, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28_value) as *mut crate::leanh::LeanObject,10540319892734294270 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__30_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value) as *mut crate::leanh::LeanObject,4034176598647545331 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value) as *mut crate::leanh::LeanObject,13806531830123099675 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28_value) as *mut crate::leanh::LeanObject,14355494118982881566 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__32_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__33_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__31_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__34_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__33_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__35_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__32_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__34_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__36_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__37_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__37_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__37_value) as *mut crate::leanh::LeanObject,3326968124746134365 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__39_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__39_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__39_value) as *mut crate::leanh::LeanObject,940684074193935882 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__41_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__41_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__41_value) as *mut crate::leanh::LeanObject,5573444893818005634 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__43_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__43_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__43_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value) as *mut crate::leanh::LeanObject,15975576917362132931 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__46_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__2_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__4_value) as *mut crate::leanh::LeanObject,4034176598647545331 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__6_value) as *mut crate::leanh::LeanObject,13806531830123099675 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__15_value) as *mut crate::leanh::LeanObject,6938991830312155811 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__48_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__47_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__49_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__48_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__50_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__50_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__50_value) as *mut crate::leanh::LeanObject,9368229134555052249 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__52_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__53_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__53_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__54_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__55_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__54_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56_value) as *mut crate::leanh::LeanObject,12014440461648055863 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__58_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__58_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__13_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__58_value) as *mut crate::leanh::LeanObject,14557702332550915328 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__61_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__62_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__62_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerSymSimpAttr___closed__11_value) as *mut crate::leanh::LeanObject,6907480769838958894 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__62_value) as *mut crate::leanh::LeanObject,16282038225239345418 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__64_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 121, 109, 46, 115, 105, 109, 112, 32, 115, 101, 116, 32, 102, 111, 114, 32, 0]};
static mut l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__64_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__12;
    v___x_525_ = l_String_toRawSubstring_x27(v___x_524_);
    return v___x_525_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__21;
    v___x_548_ = l_String_toRawSubstring_x27(v___x_547_);
    return v___x_548_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__28;
    v___x_561_ = l_String_toRawSubstring_x27(v___x_560_);
    return v___x_561_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = l_Lean_Parser_Command_registerSymSimpAttr___closed__15;
    v___x_607_ = l_String_toRawSubstring_x27(v___x_606_);
    return v___x_607_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_645_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1(
    mut v_x_653_: *mut crate::leanh::LeanObject,
    mut v_a_654_: *mut crate::leanh::LeanObject,
    mut v_a_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_809_: u8 = 0;
    let mut v___y_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v_idParser_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_848_: u8 = 0;
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_656_ = l_Lean_Parser_Command_registerSymSimpAttr___closed__0;
                v___x_657_ = l_Lean_Parser_Command_registerSymSimpAttr___closed__11;
                v___x_801_ = l_Lean_Parser_Command_registerSymSimpAttr___closed__16;
                crate::leanh::lean_inc(v_x_653_);
                v___x_802_ = l_Lean_Syntax_isOfKind(v_x_653_, v___x_801_);
                if v___x_802_ == 0 {
                    crate::leanh::lean_dec(v_x_653_);
                    v___x_803_ = crate::leanh::lean_box(1);
                    v___x_804_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_804_, 0, v___x_803_);
                    crate::leanh::lean_ctor_set(v___x_804_, 1, v_a_655_);
                    return v___x_804_;
                } else {
                    v___x_805_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_828_ = l_Lean_Syntax_getArg(v_x_653_, v___x_805_);
                    v___x_829_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_id_830_ = l_Lean_Syntax_getArg(v_x_653_, v___x_829_);
                    crate::leanh::lean_dec(v_x_653_);
                    v___x_843_ = l_Lean_Syntax_getOptional_x3f(v___x_828_);
                    crate::leanh::lean_dec(v___x_828_);
                    if crate::leanh::lean_obj_tag(v___x_843_) == 0 {
                        v___x_844_ = crate::leanh::lean_box(0);
                        v___y_832_ = v___x_844_;
                        state = 4;
                        continue;
                    } else {
                        v_val_845_ = crate::leanh::lean_ctor_get(v___x_843_, 0);
                        v_isSharedCheck_852_ = (!crate::leanh::lean_is_exclusive(v___x_843_)) as u8;
                        if v_isSharedCheck_852_ == 0 {
                            v___x_847_ = v___x_843_;
                            v_isShared_848_ = v_isSharedCheck_852_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_845_);
                            crate::leanh::lean_dec(v___x_843_);
                            v___x_847_ = crate::leanh::lean_box(0);
                            v_isShared_848_ = v_isSharedCheck_852_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v___y_660_, 5);
                crate::leanh::lean_inc_n(v___y_680_, 19);
                v___x_682_ = l_Lean_Syntax_node2(v___y_680_, v___y_660_, v___y_681_, v___y_666_);
                crate::leanh::lean_inc(v___y_664_);
                v___x_683_ = l_Lean_Syntax_node2(v___y_680_, v___y_664_, v___y_669_, v___x_682_);
                crate::leanh::lean_inc(v___y_667_);
                v___x_684_ = l_Lean_Syntax_node1(v___y_680_, v___y_667_, v___x_683_);
                crate::leanh::lean_inc_n(v___y_675_, 4);
                crate::leanh::lean_inc(v___y_659_);
                v___x_685_ = l_Lean_Syntax_node2(v___y_680_, v___y_659_, v___x_684_, v___y_675_);
                v___x_686_ = l_Lean_Syntax_node1(v___y_680_, v___y_660_, v___x_685_);
                crate::leanh::lean_inc(v___y_663_);
                v___x_687_ = l_Lean_Syntax_node1(v___y_680_, v___y_663_, v___x_686_);
                crate::leanh::lean_inc(v___y_674_);
                v___x_688_ = l_Lean_Syntax_node4(
                    v___y_680_, v___y_674_, v___y_665_, v___y_661_, v___y_678_, v___x_687_,
                );
                v___x_689_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__0;
                v___x_690_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__1;
                v___x_691_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__2;
                crate::leanh::lean_inc_ref(v___y_677_);
                v___x_692_ = l_Lean_Name_mkStr4(v___x_656_, v___x_657_, v___y_677_, v___x_691_);
                v___x_693_ = l_Lean_Syntax_node1(v___y_680_, v___x_692_, v___y_675_);
                v___x_694_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_694_, 0, v___y_680_);
                crate::leanh::lean_ctor_set(v___x_694_, 1, v___x_689_);
                v___x_695_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__4;
                v___x_696_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__5;
                v___x_697_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_697_, 0, v___y_680_);
                crate::leanh::lean_ctor_set(v___x_697_, 1, v___x_696_);
                v___x_698_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__6;
                v___x_699_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_699_, 0, v___y_680_);
                crate::leanh::lean_ctor_set(v___x_699_, 1, v___x_698_);
                v___x_700_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__7;
                v___x_701_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_701_, 0, v___y_680_);
                crate::leanh::lean_ctor_set(v___x_701_, 1, v___x_700_);
                v___x_702_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__8;
                v___x_703_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_703_, 0, v___y_680_);
                crate::leanh::lean_ctor_set(v___x_703_, 1, v___x_702_);
                v___x_704_ = l_Lean_Syntax_node5(
                    v___y_680_, v___x_695_, v___x_697_, v___x_699_, v___x_701_, v___y_671_,
                    v___x_703_,
                );
                v___x_705_ = l_Lean_Syntax_node1(v___y_680_, v___y_660_, v___x_704_);
                v___x_706_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__11;
                v___x_707_ = l_Lean_Syntax_mkStrLit(v___y_668_, v___y_670_);
                v___x_708_ = l_Lean_Syntax_node1(v___y_680_, v___x_706_, v___x_707_);
                v___x_709_ = l_Lean_Syntax_node1(v___y_680_, v___y_660_, v___x_708_);
                v___x_710_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13_once), _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__13);
                v___x_711_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__14;
                crate::leanh::lean_inc(v___y_679_);
                crate::leanh::lean_inc(v___y_672_);
                v___x_712_ = l_Lean_addMacroScope(v___y_672_, v___x_711_, v___y_679_);
                v___x_713_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_713_, 0, v___y_680_);
                crate::leanh::lean_ctor_set(v___x_713_, 1, v___x_710_);
                crate::leanh::lean_ctor_set(v___x_713_, 2, v___x_712_);
                crate::leanh::lean_ctor_set(v___x_713_, 3, v___y_673_);
                v___x_714_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_715_ = lean_mk_empty_array_with_capacity(v___x_714_);
                v___x_716_ = lean_array_push(v___x_715_, v___y_676_);
                v___x_717_ = lean_array_push(v___x_716_, v___y_675_);
                v___x_718_ = lean_array_push(v___x_717_, v___x_693_);
                v___x_719_ = lean_array_push(v___x_718_, v___x_694_);
                v___x_720_ = lean_array_push(v___x_719_, v___y_675_);
                v___x_721_ = lean_array_push(v___x_720_, v___x_705_);
                v___x_722_ = lean_array_push(v___x_721_, v___y_675_);
                v___x_723_ = lean_array_push(v___x_722_, v___x_709_);
                v___x_724_ = lean_array_push(v___x_723_, v___y_662_);
                v___x_725_ = lean_array_push(v___x_724_, v___x_713_);
                v___x_726_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_726_, 0, v___y_680_);
                crate::leanh::lean_ctor_set(v___x_726_, 1, v___x_690_);
                crate::leanh::lean_ctor_set(v___x_726_, 2, v___x_725_);
                v___x_727_ = l_Lean_Syntax_node2(v___y_680_, v___y_660_, v___x_688_, v___x_726_);
                v___x_728_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_728_, 0, v___x_727_);
                crate::leanh::lean_ctor_set(v___x_728_, 1, v_a_655_);
                return v___x_728_;
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_731_, 2);
                v___x_744_ = l_Array_append___redArg(v___y_731_, v___y_743_);
                crate::leanh::lean_dec_ref(v___y_743_);
                crate::leanh::lean_inc_n(v___y_730_, 5);
                crate::leanh::lean_inc_n(v___y_741_, 18);
                v___x_745_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_745_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_745_, 1, v___y_730_);
                crate::leanh::lean_ctor_set(v___x_745_, 2, v___x_744_);
                v___x_746_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_746_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_746_, 1, v___y_730_);
                crate::leanh::lean_ctor_set(v___x_746_, 2, v___y_731_);
                v___x_747_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__15;
                v___x_748_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__16;
                v___x_749_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_749_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_749_, 1, v___x_747_);
                v___x_750_ = l_Lean_Syntax_node1(v___y_741_, v___x_748_, v___x_749_);
                v___x_751_ = l_Lean_Syntax_node1(v___y_741_, v___y_730_, v___x_750_);
                v___x_752_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__17;
                v___x_753_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__18;
                v___x_754_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_754_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_754_, 1, v___x_752_);
                v___x_755_ = l_Lean_Syntax_node1(v___y_741_, v___x_753_, v___x_754_);
                v___x_756_ = l_Lean_Syntax_node1(v___y_741_, v___y_730_, v___x_755_);
                crate::leanh::lean_inc_ref_n(v___x_746_, 4);
                crate::leanh::lean_inc_ref(v___x_745_);
                crate::leanh::lean_inc(v___y_740_);
                v___x_757_ = l_Lean_Syntax_node7(
                    v___y_741_, v___y_740_, v___x_745_, v___x_746_, v___x_751_, v___x_746_,
                    v___x_756_, v___x_746_, v___x_746_,
                );
                v___x_758_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__20;
                crate::leanh::lean_inc_ref(v___y_739_);
                v___x_759_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_759_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_759_, 1, v___y_739_);
                v___x_760_ = l_Lean_Syntax_node1(v___y_741_, v___x_758_, v___x_759_);
                v___x_761_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22_once), _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__22);
                v___x_762_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__23;
                crate::leanh::lean_inc_n(v___y_742_, 3);
                crate::leanh::lean_inc_n(v___y_737_, 3);
                v___x_763_ = l_Lean_addMacroScope(v___y_737_, v___x_762_, v___y_742_);
                v___x_764_ = crate::leanh::lean_box(0);
                v___x_765_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_765_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_765_, 1, v___x_761_);
                crate::leanh::lean_ctor_set(v___x_765_, 2, v___x_763_);
                crate::leanh::lean_ctor_set(v___x_765_, 3, v___x_764_);
                v___x_766_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__24;
                v___x_767_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__26;
                v___x_768_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__27;
                v___x_769_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_769_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_769_, 1, v___x_768_);
                v___x_770_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29_once), _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__29);
                v___x_771_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__30;
                v___x_772_ = l_Lean_addMacroScope(v___y_737_, v___x_771_, v___y_742_);
                v___x_773_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__35;
                v___x_774_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_774_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_774_, 1, v___x_770_);
                crate::leanh::lean_ctor_set(v___x_774_, 2, v___x_772_);
                crate::leanh::lean_ctor_set(v___x_774_, 3, v___x_773_);
                crate::leanh::lean_inc_ref(v___x_769_);
                v___x_775_ = l_Lean_Syntax_node2(v___y_741_, v___x_767_, v___x_769_, v___x_774_);
                v___x_776_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__36;
                v___x_777_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_777_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_777_, 1, v___x_776_);
                v___x_778_ =
                    l_Lean_Syntax_node3(v___y_741_, v___y_730_, v___x_765_, v___x_775_, v___x_777_);
                v___x_779_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__38;
                v___x_780_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__40;
                v___x_781_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__42;
                v___x_782_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__44;
                v___x_783_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45_once), _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__45);
                v___x_784_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__46;
                v___x_785_ = l_Lean_addMacroScope(v___y_737_, v___x_784_, v___y_742_);
                v___x_786_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__49;
                v___x_787_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_787_, 0, v___y_741_);
                crate::leanh::lean_ctor_set(v___x_787_, 1, v___x_783_);
                crate::leanh::lean_ctor_set(v___x_787_, 2, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_787_, 3, v___x_786_);
                crate::leanh::lean_inc(v___y_734_);
                v___x_788_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_764_, v___y_734_,
                );
                if crate::leanh::lean_obj_tag(v___x_788_) == 0 {
                    v___x_789_ = l_Lean_quoteNameMk(v___y_734_);
                    v___y_659_ = v___x_780_;
                    v___y_660_ = v___y_730_;
                    v___y_661_ = v___x_760_;
                    v___y_662_ = v___x_769_;
                    v___y_663_ = v___x_779_;
                    v___y_664_ = v___x_782_;
                    v___y_665_ = v___x_757_;
                    v___y_666_ = v___y_732_;
                    v___y_667_ = v___x_781_;
                    v___y_668_ = v___y_733_;
                    v___y_669_ = v___x_787_;
                    v___y_670_ = v___y_735_;
                    v___y_671_ = v___y_736_;
                    v___y_672_ = v___y_737_;
                    v___y_673_ = v___x_764_;
                    v___y_674_ = v___y_738_;
                    v___y_675_ = v___x_746_;
                    v___y_676_ = v___x_745_;
                    v___y_677_ = v___x_766_;
                    v___y_678_ = v___x_778_;
                    v___y_679_ = v___y_742_;
                    v___y_680_ = v___y_741_;
                    v___y_681_ = v___x_789_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_734_);
                    v_val_790_ = crate::leanh::lean_ctor_get(v___x_788_, 0);
                    crate::leanh::lean_inc(v_val_790_);
                    crate::leanh::lean_dec_ref_known(v___x_788_, 1);
                    v___x_791_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__51;
                    v___x_792_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__52;
                    v___x_793_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__53;
                    v___x_794_ = lean_string_intercalate(v___x_793_, v_val_790_);
                    v___x_795_ = lean_string_append(v___x_792_, v___x_794_);
                    crate::leanh::lean_dec_ref(v___x_794_);
                    crate::leanh::lean_inc_n(v___y_735_, 2);
                    v___x_796_ = l_Lean_Syntax_mkNameLit(v___x_795_, v___y_735_);
                    v___x_797_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_798_ = lean_mk_empty_array_with_capacity(v___x_797_);
                    v___x_799_ = lean_array_push(v___x_798_, v___x_796_);
                    v___x_800_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_800_, 0, v___y_735_);
                    crate::leanh::lean_ctor_set(v___x_800_, 1, v___x_791_);
                    crate::leanh::lean_ctor_set(v___x_800_, 2, v___x_799_);
                    v___y_659_ = v___x_780_;
                    v___y_660_ = v___y_730_;
                    v___y_661_ = v___x_760_;
                    v___y_662_ = v___x_769_;
                    v___y_663_ = v___x_779_;
                    v___y_664_ = v___x_782_;
                    v___y_665_ = v___x_757_;
                    v___y_666_ = v___y_732_;
                    v___y_667_ = v___x_781_;
                    v___y_668_ = v___y_733_;
                    v___y_669_ = v___x_787_;
                    v___y_670_ = v___y_735_;
                    v___y_671_ = v___y_736_;
                    v___y_672_ = v___y_737_;
                    v___y_673_ = v___x_764_;
                    v___y_674_ = v___y_738_;
                    v___y_675_ = v___x_746_;
                    v___y_676_ = v___x_745_;
                    v___y_677_ = v___x_766_;
                    v___y_678_ = v___x_778_;
                    v___y_679_ = v___y_742_;
                    v___y_680_ = v___y_741_;
                    v___y_681_ = v___x_800_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_quotContext_813_ = crate::leanh::lean_ctor_get(v_a_654_, 1);
                v_currMacroScope_814_ = crate::leanh::lean_ctor_get(v_a_654_, 2);
                v_ref_815_ = crate::leanh::lean_ctor_get(v_a_654_, 5);
                v___x_816_ = l_String_removeLeadingSpaces(v___y_812_);
                v___x_817_ = crate::leanh::lean_box(2);
                v___x_818_ = l_Lean_Syntax_mkStrLit(v___x_816_, v___x_817_);
                v___x_819_ = l_Lean_SourceInfo_fromRef(v_ref_815_, v___y_809_);
                v___x_820_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__55;
                v___x_821_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__56;
                v___x_822_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__57;
                v___x_823_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__59;
                v___x_824_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60_once), _init_l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__60);
                if crate::leanh::lean_obj_tag(v___y_808_) == 1 {
                    v_val_825_ = crate::leanh::lean_ctor_get(v___y_808_, 0);
                    crate::leanh::lean_inc(v_val_825_);
                    crate::leanh::lean_dec_ref_known(v___y_808_, 1);
                    v___x_826_ = l_Array_mkArray1___redArg(v_val_825_);
                    v___y_730_ = v___x_820_;
                    v___y_731_ = v___x_824_;
                    v___y_732_ = v___x_818_;
                    v___y_733_ = v___y_811_;
                    v___y_734_ = v___y_810_;
                    v___y_735_ = v___x_817_;
                    v___y_736_ = v___y_807_;
                    v___y_737_ = v_quotContext_813_;
                    v___y_738_ = v___x_822_;
                    v___y_739_ = v___x_821_;
                    v___y_740_ = v___x_823_;
                    v___y_741_ = v___x_819_;
                    v___y_742_ = v_currMacroScope_814_;
                    v___y_743_ = v___x_826_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_808_);
                    v___x_827_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__61;
                    v___y_730_ = v___x_820_;
                    v___y_731_ = v___x_824_;
                    v___y_732_ = v___x_818_;
                    v___y_733_ = v___y_811_;
                    v___y_734_ = v___y_810_;
                    v___y_735_ = v___x_817_;
                    v___y_736_ = v___y_807_;
                    v___y_737_ = v_quotContext_813_;
                    v___y_738_ = v___x_822_;
                    v___y_739_ = v___x_821_;
                    v___y_740_ = v___x_823_;
                    v___y_741_ = v___x_819_;
                    v___y_742_ = v_currMacroScope_814_;
                    v___y_743_ = v___x_827_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_833_ = l_Lean_TSyntax_getId(v_id_830_);
                crate::leanh::lean_inc_n(v___x_833_, 2);
                v_str_834_ = l_Lean_Name_toString(v___x_833_, v___x_802_);
                v___x_835_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__63;
                v___x_836_ = l_Lean_Name_append(v___x_835_, v___x_833_);
                v___x_837_ = 0;
                v_idParser_838_ = l_Lean_mkIdentFrom(v_id_830_, v___x_836_, v___x_837_);
                crate::leanh::lean_dec(v_id_830_);
                if crate::leanh::lean_obj_tag(v___y_832_) == 0 {
                    v___x_839_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___closed__64;
                    v___x_840_ = lean_string_append(v___x_839_, v_str_834_);
                    v___y_807_ = v_idParser_838_;
                    v___y_808_ = v___y_832_;
                    v___y_809_ = v___x_837_;
                    v___y_810_ = v___x_833_;
                    v___y_811_ = v_str_834_;
                    v___y_812_ = v___x_840_;
                    state = 3;
                    continue;
                } else {
                    v_val_841_ = crate::leanh::lean_ctor_get(v___y_832_, 0);
                    v___x_842_ = l_Lean_TSyntax_getDocString(v_val_841_);
                    v___y_807_ = v_idParser_838_;
                    v___y_808_ = v___y_832_;
                    v___y_809_ = v___x_837_;
                    v___y_810_ = v___x_833_;
                    v___y_811_ = v_str_834_;
                    v___y_812_ = v___x_842_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                if v_isShared_848_ == 0 {
                    v___x_850_ = v___x_847_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_851_, 0, v_val_845_);
                    v___x_850_ = v_reuseFailAlloc_851_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_832_ = v___x_850_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1___boxed(
    mut v_x_853_: *mut crate::leanh::LeanObject,
    mut v_a_854_: *mut crate::leanh::LeanObject,
    mut v_a_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_856_ = l_Lean_Meta_Sym_Simp___aux__Lean__Meta__Sym__Simp__RegisterCommand______macroRules__Lean__Meta__Sym__Simp____root____Lean__Parser__Command__registerSymSimpAttr__1(v_x_853_, v_a_854_, v_a_855_);
    crate::leanh::lean_dec_ref(v_a_854_);
    return v_res_856_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_RegisterCommand(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_RegisterCommand(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_RegisterCommand(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Variant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
}
