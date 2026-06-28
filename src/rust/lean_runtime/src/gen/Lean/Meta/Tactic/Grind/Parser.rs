// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Parser
// Imports: Lean.Parser.Command
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6,
};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthen, l_Lean_Parser_atomic, l_Lean_Parser_checkColGe,
    l_Lean_Parser_leadingNode, l_Lean_Parser_mkAntiquot, l_Lean_Parser_nonReservedSymbol,
    l_Lean_Parser_orelse, l_Lean_Parser_sepBy1, l_Lean_Parser_skip, l_Lean_Parser_symbol,
    l_Lean_Parser_termParser, l_Lean_Parser_withAntiquot, l_Lean_Parser_withPosition,
};
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::Parser::Extension::l_Lean_Parser_addBuiltinLeadingParser;
use crate::r#gen::Lean::Parser::Extra::{
    l_Lean_Parser_atomic_formatter___boxed, l_Lean_Parser_ident,
    l_Lean_Parser_ident_formatter___boxed, l_Lean_Parser_ident_parenthesizer___boxed,
    l_Lean_Parser_leadingNode_formatter___boxed, l_Lean_Parser_many,
    l_Lean_Parser_many_formatter___boxed, l_Lean_Parser_many_parenthesizer___boxed,
    l_Lean_Parser_many1, l_Lean_Parser_many1Indent_formatter___boxed,
    l_Lean_Parser_many1Indent_parenthesizer___boxed, l_Lean_Parser_mkAntiquot_formatter___boxed,
    l_Lean_Parser_mkAntiquot_parenthesizer___boxed,
    l_Lean_Parser_nonReservedSymbol_formatter___boxed,
    l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, l_Lean_Parser_numLit,
    l_Lean_Parser_numLit_formatter___boxed, l_Lean_Parser_numLit_parenthesizer___boxed,
    l_Lean_Parser_optional, l_Lean_Parser_optional_formatter___boxed,
    l_Lean_Parser_optional_parenthesizer___boxed, l_Lean_Parser_ppLine_parenthesizer___boxed,
    l_Lean_Parser_sepBy1_formatter___boxed, l_Lean_Parser_sepBy1_parenthesizer___boxed,
    l_Lean_Parser_symbol_formatter___boxed, l_Lean_Parser_symbol_parenthesizer___boxed,
    l_Lean_Parser_termParser_formatter___boxed, l_Lean_Parser_termParser_parenthesizer___boxed,
    l_Lean_ppLine_formatter___boxed,
};
use crate::r#gen::Lean::Parser::Term::{
    l_Lean_Parser_Term_attrKind, l_Lean_Parser_Term_attrKind_formatter___boxed,
    l_Lean_Parser_Term_attrKind_parenthesizer___boxed, l_Lean_Parser_darrow,
    l_Lean_Parser_darrow_formatter___boxed, l_Lean_Parser_darrow_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Types::l_Lean_Parser_withCache;
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed,
    l_Lean_PrettyPrinter_formatterAttribute,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_parenthesizerAttribute,
};
pub static l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value:
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
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value:
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
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value:
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
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value:
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
    m_data: [71, 114, 105, 110, 100, 67, 110, 115, 116, 114, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value:
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
    m_data: [105, 115, 86, 97, 108, 117, 101, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value)
            as *mut crate::leanh::LeanObject,
        67484279027498894 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_isValue___closed__7_value:
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
    m_data: [105, 115, 95, 118, 97, 108, 117, 101, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_isValue___closed__9_value:
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
    m_data: [59, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isValue___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_isValue: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value:
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
        105, 115, 83, 116, 114, 105, 99, 116, 86, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        1634303821783410512 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3_value:
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
        105, 115, 95, 115, 116, 114, 105, 99, 116, 95, 118, 97, 108, 117, 101, 32, 0,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value:
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
    m_data: [110, 111, 116, 86, 97, 108, 117, 101, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        358054841606714373 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_notValue___closed__3_value:
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
    m_data: [110, 111, 116, 95, 118, 97, 108, 117, 101, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notValue___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_notValue: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        110, 111, 116, 83, 116, 114, 105, 99, 116, 86, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6009541856878394148 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3_value:
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
        110, 111, 116, 95, 115, 116, 114, 105, 99, 116, 95, 118, 97, 108, 117, 101, 32, 0,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value:
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
    m_data: [105, 115, 71, 114, 111, 117, 110, 100, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12776886811539497825 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_isGround___closed__3_value:
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
    m_data: [105, 115, 95, 103, 114, 111, 117, 110, 100, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_isGround___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_isGround: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value:
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
    m_data: [115, 105, 122, 101, 76, 116, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10564253717456944082 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3_value:
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
    m_data: [115, 105, 122, 101, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5_value:
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
    m_data: [32, 60, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_sizeLt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value:
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
    m_data: [100, 101, 112, 116, 104, 76, 116, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        816581574741003704 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3_value:
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
    m_data: [100, 101, 112, 116, 104, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_depthLt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value:
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
    m_data: [103, 101, 110, 76, 116, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3440059094326707764 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_genLt___closed__3_value:
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
    m_data: [103, 101, 110, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_genLt___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_genLt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value:
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
    m_data: [109, 97, 120, 73, 110, 115, 116, 115, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value)
            as *mut crate::leanh::LeanObject,
        1572271875277745300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3_value:
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
    m_data: [109, 97, 120, 95, 105, 110, 115, 116, 115, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_maxInsts: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value:
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
    m_data: [103, 117, 97, 114, 100, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5471431434235198435 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_guard___closed__3_value:
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
    m_data: [103, 117, 97, 114, 100, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_guard___closed__5_value:
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
    m_data: [105, 114, 114, 101, 108, 101, 118, 97, 110, 116, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_guard___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_guard: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_check___closed__0_value:
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
    m_data: [99, 104, 101, 99, 107, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_check___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16996207256393601998 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_check___closed__3_value:
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
    m_data: [99, 104, 101, 99, 107, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_check___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_check: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value:
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
    m_data: [110, 111, 116, 68, 101, 102, 69, 113, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12235799381117781943 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3_value:
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
    m_data: [32, 61, 47, 61, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_notDefEq: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value:
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
    m_data: [100, 101, 102, 69, 113, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7587423409180122123 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12510525609298890846 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_GrindCnstr_defEq___closed__3_value:
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
    m_data: [32, 61, 63, 61, 32, 0],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_GrindCnstr_defEq___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_GrindCnstr_defEq: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_grindPatternCnstr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value:
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
        103, 114, 105, 110, 100, 80, 97, 116, 116, 101, 114, 110, 67, 110, 115, 116, 114, 115, 0,
    ],
};
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2874757003574178313 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPatternCnstrs___closed__3_value:
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
    m_data: [119, 104, 101, 114, 101, 32, 0],
};
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPatternCnstrs___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_grindPatternCnstrs: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPattern___closed__0_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [103, 114, 105, 110, 100, 80, 97, 116, 116, 101, 114, 110, 0],
};
static mut l_Lean_Parser_Command_grindPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_grindPattern___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Command_grindPattern___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Command_grindPattern___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Command_grindPattern___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2214494411411724007 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_grindPattern___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPattern___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPattern___closed__3_value: crate::leanh::LeanStringObject<
    15,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        103, 114, 105, 110, 100, 95, 112, 97, 116, 116, 101, 114, 110, 32, 0,
    ],
};
static mut l_Lean_Parser_Command_grindPattern___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPattern___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPattern___closed__5_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_Parser_Command_grindPattern___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPattern___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPattern___closed__7_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_Parser_Command_grindPattern___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPattern___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPattern___closed__12_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Parser_Command_grindPattern___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPattern___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_grindPattern___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_grindPattern: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__0_value) as *mut crate::leanh::LeanObject,5063646790596052253 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0_value: crate::leanh::LeanStringObject<4114> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4114, m_capacity: 4114, m_length: 4060, m_data: [84, 104, 101, 32, 96, 103, 114, 105, 110, 100, 95, 112, 97, 116, 116, 101, 114, 110, 96, 32, 99, 111, 109, 109, 97, 110, 100, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 116, 111, 32, 109, 97, 110, 117, 97, 108, 108, 121, 32, 115, 101, 108, 101, 99, 116, 32, 97, 32, 112, 97, 116, 116, 101, 114, 110, 32, 102, 111, 114, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 111, 110, 46, 10, 69, 110, 97, 98, 108, 105, 110, 103, 32, 116, 104, 101, 32, 111, 112, 116, 105, 111, 110, 32, 96, 116, 114, 97, 99, 101, 46, 103, 114, 105, 110, 100, 46, 101, 109, 97, 116, 99, 104, 46, 105, 110, 115, 116, 97, 110, 99, 101, 96, 32, 99, 97, 117, 115, 101, 115, 32, 96, 103, 114, 105, 110, 100, 96, 32, 116, 111, 32, 112, 114, 105, 110, 116, 32, 97, 32, 116, 114, 97, 99, 101, 32, 109, 101, 115, 115, 97, 103, 101, 32, 102, 111, 114, 32, 101, 97, 99, 104, 10, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 116, 32, 103, 101, 110, 101, 114, 97, 116, 101, 115, 44, 32, 119, 104, 105, 99, 104, 32, 99, 97, 110, 32, 98, 101, 32, 104, 101, 108, 112, 102, 117, 108, 32, 119, 104, 101, 110, 32, 100, 101, 116, 101, 114, 109, 105, 110, 105, 110, 103, 32, 112, 97, 116, 116, 101, 114, 110, 115, 46, 10, 10, 87, 104, 101, 110, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32, 112, 97, 116, 116, 101, 114, 110, 115, 32, 97, 114, 101, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 116, 111, 103, 101, 116, 104, 101, 114, 44, 32, 97, 108, 108, 32, 111, 102, 32, 116, 104, 101, 109, 32, 109, 117, 115, 116, 32, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 99, 111, 110, 116, 101, 120, 116, 32, 98, 101, 102, 111, 114, 101, 10, 96, 103, 114, 105, 110, 100, 96, 32, 97, 116, 116, 101, 109, 112, 116, 115, 32, 116, 111, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 114, 101, 102, 101, 114, 114, 101, 100, 32, 116, 111, 32, 97, 115, 32, 97, 32, 42, 109, 117, 108, 116, 105, 45, 112, 97, 116, 116, 101, 114, 110, 42, 46, 10, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 116, 114, 97, 110, 115, 105, 116, 105, 118, 105, 116, 121, 32, 114, 117, 108, 101, 115, 44, 32, 119, 104, 101, 114, 101, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32, 112, 114, 101, 109, 105, 115, 101, 115, 32, 109, 117, 115, 116, 32, 98, 101, 32, 115, 105, 109, 117, 108, 116, 97, 110, 101, 111, 117, 115, 108, 121, 10, 112, 114, 101, 115, 101, 110, 116, 32, 102, 111, 114, 32, 116, 104, 101, 32, 114, 117, 108, 101, 32, 116, 111, 32, 97, 112, 112, 108, 121, 46, 10, 10, 73, 110, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 101, 120, 97, 109, 112, 108, 101, 44, 32, 96, 82, 96, 32, 105, 115, 32, 97, 32, 116, 114, 97, 110, 115, 105, 116, 105, 118, 101, 32, 98, 105, 110, 97, 114, 121, 32, 114, 101, 108, 97, 116, 105, 111, 110, 32, 111, 118, 101, 114, 32, 96, 73, 110, 116, 96, 46, 10, 96, 96, 96, 10, 111, 112, 97, 113, 117, 101, 32, 82, 32, 58, 32, 73, 110, 116, 32, 226, 134, 146, 32, 73, 110, 116, 32, 226, 134, 146, 32, 80, 114, 111, 112, 10, 97, 120, 105, 111, 109, 32, 82, 116, 114, 97, 110, 115, 32, 123, 120, 32, 121, 32, 122, 32, 58, 32, 73, 110, 116, 125, 32, 58, 32, 82, 32, 120, 32, 121, 32, 226, 134, 146, 32, 82, 32, 121, 32, 122, 32, 226, 134, 146, 32, 82, 32, 120, 32, 122, 10, 96, 96, 96, 10, 84, 111, 32, 117, 115, 101, 32, 116, 104, 101, 32, 102, 97, 99, 116, 32, 116, 104, 97, 116, 32, 96, 82, 96, 32, 105, 115, 32, 116, 114, 97, 110, 115, 105, 116, 105, 118, 101, 44, 32, 96, 103, 114, 105, 110, 100, 96, 32, 109, 117, 115, 116, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 32, 97, 98, 108, 101, 32, 116, 111, 32, 115, 97, 116, 105, 115, 102, 121, 32, 98, 111, 116, 104, 32, 112, 114, 101, 109, 105, 115, 101, 115, 46, 10, 84, 104, 105, 115, 32, 105, 115, 32, 114, 101, 112, 114, 101, 115, 101, 110, 116, 101, 100, 32, 117, 115, 105, 110, 103, 32, 97, 32, 109, 117, 108, 116, 105, 45, 112, 97, 116, 116, 101, 114, 110, 58, 10, 96, 96, 96, 10, 103, 114, 105, 110, 100, 95, 112, 97, 116, 116, 101, 114, 110, 32, 82, 116, 114, 97, 110, 115, 32, 61, 62, 32, 82, 32, 120, 32, 121, 44, 32, 82, 32, 121, 32, 122, 10, 10, 101, 120, 97, 109, 112, 108, 101, 32, 123, 97, 32, 98, 32, 99, 32, 100, 125, 32, 58, 32, 82, 32, 97, 32, 98, 32, 226, 134, 146, 32, 82, 32, 98, 32, 99, 32, 226, 134, 146, 32, 82, 32, 99, 32, 100, 32, 226, 134, 146, 32, 82, 32, 97, 32, 100, 32, 58, 61, 32, 98, 121, 10, 32, 32, 103, 114, 105, 110, 100, 10, 96, 96, 96, 10, 84, 104, 101, 32, 109, 117, 108, 116, 105, 45, 112, 97, 116, 116, 101, 114, 110, 32, 96, 82, 32, 120, 32, 121, 96, 44, 32, 96, 82, 32, 121, 32, 122, 96, 32, 105, 110, 115, 116, 114, 117, 99, 116, 115, 32, 96, 103, 114, 105, 110, 100, 96, 32, 116, 111, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 96, 82, 116, 114, 97, 110, 115, 96, 32, 111, 110, 108, 121, 32, 119, 104, 101, 110, 32, 98, 111, 116, 104, 32, 96, 82, 32, 120, 32, 121, 96, 10, 97, 110, 100, 32, 96, 82, 32, 121, 32, 122, 96, 32, 97, 114, 101, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 110, 116, 101, 120, 116, 46, 32, 73, 110, 32, 116, 104, 101, 32, 101, 120, 97, 109, 112, 108, 101, 44, 32, 96, 103, 114, 105, 110, 100, 96, 32, 97, 112, 112, 108, 105, 101, 115, 32, 96, 82, 116, 114, 97, 110, 115, 96, 32, 116, 111, 32, 100, 101, 114, 105, 118, 101, 32, 96, 82, 32, 97, 32, 99, 96, 10, 102, 114, 111, 109, 32, 96, 82, 32, 97, 32, 98, 96, 32, 97, 110, 100, 32, 96, 82, 32, 98, 32, 99, 96, 44, 32, 97, 110, 100, 32, 99, 97, 110, 32, 116, 104, 101, 110, 32, 114, 101, 112, 101, 97, 116, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 114, 101, 97, 115, 111, 110, 105, 110, 103, 32, 116, 111, 32, 100, 101, 100, 117, 99, 101, 32, 96, 82, 32, 97, 32, 100, 96, 32, 102, 114, 111, 109, 32, 96, 82, 32, 97, 32, 99, 96, 32, 97, 110, 100, 10, 96, 82, 32, 99, 32, 100, 96, 46, 10, 10, 89, 111, 117, 32, 99, 97, 110, 32, 97, 100, 100, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 115, 32, 116, 111, 32, 114, 101, 115, 116, 114, 105, 99, 116, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 111, 110, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 58, 10, 96, 96, 96, 10, 103, 114, 105, 110, 100, 95, 112, 97, 116, 116, 101, 114, 110, 32, 101, 120, 116, 114, 97, 99, 116, 95, 101, 120, 116, 114, 97, 99, 116, 32, 61, 62, 32, 40, 97, 115, 46, 101, 120, 116, 114, 97, 99, 116, 32, 105, 32, 106, 41, 46, 101, 120, 116, 114, 97, 99, 116, 32, 107, 32, 108, 32, 119, 104, 101, 114, 101, 10, 32, 32, 97, 115, 32, 61, 47, 61, 32, 35, 91, 93, 10, 96, 96, 96, 10, 84, 104, 101, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 32, 105, 110, 115, 116, 114, 117, 99, 116, 115, 32, 96, 103, 114, 105, 110, 100, 96, 32, 116, 111, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 111, 110, 108, 121, 32, 105, 102, 32, 96, 97, 115, 96, 32, 105, 115, 32, 42, 42, 110, 111, 116, 42, 42, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 10, 116, 111, 32, 96, 35, 91, 93, 96, 46, 10, 10, 35, 35, 32, 67, 111, 110, 115, 116, 114, 97, 105, 110, 116, 115, 10, 10, 45, 32, 96, 120, 32, 61, 47, 61, 32, 116, 101, 114, 109, 96, 58, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 98, 111, 117, 110, 100, 32, 116, 111, 32, 96, 120, 96, 32, 40, 111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 41, 32, 105, 115, 32, 42, 42, 110, 111, 116, 42, 42, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 96, 116, 101, 114, 109, 96, 46, 10, 32, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 109, 97, 121, 32, 99, 111, 110, 116, 97, 105, 110, 32, 104, 111, 108, 101, 115, 32, 40, 105, 46, 101, 46, 44, 32, 96, 95, 96, 41, 46, 10, 10, 45, 32, 96, 120, 32, 61, 63, 61, 32, 116, 101, 114, 109, 96, 58, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 98, 111, 117, 110, 100, 32, 116, 111, 32, 96, 120, 96, 32, 105, 115, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 96, 116, 101, 114, 109, 96, 46, 10, 32, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 109, 97, 121, 32, 99, 111, 110, 116, 97, 105, 110, 32, 104, 111, 108, 101, 115, 32, 40, 105, 46, 101, 46, 44, 32, 96, 95, 96, 41, 46, 10, 10, 45, 32, 96, 115, 105, 122, 101, 32, 120, 32, 60, 32, 110, 96, 58, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 98, 111, 117, 110, 100, 32, 116, 111, 32, 96, 120, 96, 32, 104, 97, 115, 32, 115, 105, 122, 101, 32, 108, 101, 115, 115, 32, 116, 104, 97, 110, 32, 96, 110, 96, 46, 32, 73, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 10, 97, 110, 100, 32, 98, 105, 110, 100, 101, 114, 32, 116, 121, 112, 101, 115, 32, 97, 114, 101, 32, 105, 103, 110, 111, 114, 101, 100, 32, 119, 104, 101, 110, 32, 99, 111, 109, 112, 117, 116, 105, 110, 103, 32, 116, 104, 101, 32, 115, 105, 122, 101, 46, 10, 10, 45, 32, 96, 100, 101, 112, 116, 104, 32, 120, 32, 60, 32, 110, 96, 58, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 98, 111, 117, 110, 100, 32, 116, 111, 32, 96, 120, 96, 32, 104, 97, 115, 32, 100, 101, 112, 116, 104, 32, 108, 101, 115, 115, 32, 116, 104, 97, 110, 32, 96, 110, 96, 46, 10, 10, 45, 32, 96, 105, 115, 95, 103, 114, 111, 117, 110, 100, 32, 120, 96, 58, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 98, 111, 117, 110, 100, 32, 116, 111, 32, 96, 120, 96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 108, 111, 99, 97, 108, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 111, 114, 32, 109, 101, 116, 97, 45, 118, 97, 114, 105, 97, 98, 108, 101, 115, 46, 10, 10, 45, 32, 96, 105, 115, 95, 118, 97, 108, 117, 101, 32, 120, 96, 58, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 98, 111, 117, 110, 100, 32, 116, 111, 32, 96, 120, 96, 32, 105, 115, 32, 97, 32, 118, 97, 108, 117, 101, 46, 32, 84, 104, 97, 116, 32, 105, 115, 44, 32, 105, 116, 32, 105, 115, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 102, 117, 108, 108, 121, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111, 32, 118, 97, 108, 117, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 44, 10, 97, 32, 108, 105, 116, 101, 114, 97, 108, 32, 40, 96, 78, 97, 116, 96, 44, 32, 96, 73, 110, 116, 96, 44, 32, 96, 83, 116, 114, 105, 110, 103, 96, 44, 32, 101, 116, 99, 46, 41, 44, 32, 111, 114, 32, 97, 32, 108, 97, 109, 98, 100, 97, 32, 96, 102, 117, 110, 32, 120, 32, 61, 62, 32, 116, 96, 46, 10, 10, 45, 32, 96, 105, 115, 95, 115, 116, 114, 105, 99, 116, 95, 118, 97, 108, 117, 101, 32, 120, 96, 58, 32, 83, 105, 109, 105, 108, 97, 114, 32, 116, 111, 32, 96, 105, 115, 95, 118, 97, 108, 117, 101, 96, 44, 32, 98, 117, 116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 108, 97, 109, 98, 100, 97, 115, 46, 10, 10, 45, 32, 96, 110, 111, 116, 95, 118, 97, 108, 117, 101, 32, 120, 96, 58, 32, 84, 104, 101, 32, 116, 101, 114, 109, 32, 98, 111, 117, 110, 100, 32, 116, 111, 32, 96, 120, 96, 32, 105, 115, 32, 97, 32, 42, 42, 110, 111, 116, 42, 42, 32, 118, 97, 108, 117, 101, 32, 40, 115, 101, 101, 32, 96, 105, 115, 95, 118, 97, 108, 117, 101, 96, 41, 46, 10, 10, 45, 32, 96, 110, 111, 116, 95, 115, 116, 114, 105, 99, 116, 95, 118, 97, 108, 117, 101, 32, 120, 96, 58, 32, 83, 105, 109, 105, 108, 97, 114, 32, 116, 111, 32, 96, 110, 111, 116, 95, 118, 97, 108, 117, 101, 96, 44, 32, 98, 117, 116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 108, 97, 109, 98, 100, 97, 115, 46, 10, 10, 45, 32, 96, 103, 101, 110, 32, 60, 32, 110, 96, 58, 32, 84, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 104, 97, 115, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 32, 108, 101, 115, 115, 32, 116, 104, 97, 110, 32, 96, 110, 96, 46, 32, 82, 101, 99, 97, 108, 108, 32, 116, 104, 97, 116, 32, 101, 97, 99, 104, 32, 116, 101, 114, 109, 32, 105, 115, 32, 97, 115, 115, 105, 103, 110, 101, 100, 32, 97, 10, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 44, 32, 97, 110, 100, 32, 116, 101, 114, 109, 115, 32, 112, 114, 111, 100, 117, 99, 101, 100, 32, 98, 121, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 111, 110, 32, 104, 97, 118, 101, 32, 97, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 32, 116, 104, 97, 116, 32, 105, 115, 32, 111, 110, 101, 32, 103, 114, 101, 97, 116, 101, 114, 32, 116, 104, 97, 110, 10, 116, 104, 101, 32, 109, 97, 120, 105, 109, 97, 108, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97, 108, 108, 32, 116, 104, 101, 32, 116, 101, 114, 109, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 46, 32, 84, 104, 105, 115, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 32, 99, 111, 109, 112, 108, 101, 109, 101, 110, 116, 115, 10, 116, 104, 101, 32, 96, 103, 101, 110, 96, 32, 111, 112, 116, 105, 111, 110, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 105, 110, 32, 96, 103, 114, 105, 110, 100, 96, 46, 10, 10, 45, 32, 96, 109, 97, 120, 95, 105, 110, 115, 116, 115, 32, 60, 32, 110, 96, 58, 32, 65, 32, 110, 101, 119, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 115, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 108, 121, 32, 105, 102, 32, 108, 101, 115, 115, 32, 116, 104, 97, 110, 32, 96, 110, 96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 104, 97, 118, 101, 32, 98, 101, 101, 110, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 115, 111, 32, 102, 97, 114, 46, 10, 10, 45, 32, 96, 103, 117, 97, 114, 100, 32, 101, 96, 58, 32, 84, 104, 101, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 111, 110, 32, 105, 115, 32, 100, 101, 108, 97, 121, 101, 100, 32, 117, 110, 116, 105, 108, 32, 96, 103, 114, 105, 110, 100, 96, 32, 108, 101, 97, 114, 110, 115, 32, 116, 104, 97, 116, 32, 96, 101, 96, 32, 105, 115, 32, 96, 116, 114, 117, 101, 96, 32, 105, 110, 32, 116, 104, 105, 115, 32, 115, 116, 97, 116, 101, 46, 10, 10, 45, 32, 96, 99, 104, 101, 99, 107, 32, 101, 96, 58, 32, 83, 105, 109, 105, 108, 97, 114, 32, 116, 111, 32, 96, 103, 117, 97, 114, 100, 32, 101, 96, 44, 32, 98, 117, 116, 32, 96, 103, 114, 105, 110, 100, 96, 32, 99, 104, 101, 99, 107, 115, 32, 119, 104, 101, 116, 104, 101, 114, 32, 96, 101, 96, 32, 105, 115, 32, 105, 109, 112, 108, 105, 101, 100, 32, 98, 121, 32, 105, 116, 115, 32, 99, 117, 114, 114, 101, 110, 116, 32, 115, 116, 97, 116, 101, 32, 98, 121, 10, 97, 115, 115, 117, 109, 105, 110, 103, 32, 96, 194, 172, 32, 101, 96, 32, 97, 110, 100, 32, 116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 100, 101, 100, 117, 99, 101, 32, 97, 110, 32, 105, 110, 99, 111, 110, 115, 105, 115, 116, 101, 110, 99, 121, 46, 10, 10, 35, 35, 32, 69, 120, 97, 109, 112, 108, 101, 10, 10, 67, 111, 110, 115, 105, 100, 101, 114, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 101, 120, 97, 109, 112, 108, 101, 32, 119, 104, 101, 114, 101, 32, 96, 102, 96, 32, 105, 115, 32, 97, 32, 109, 111, 110, 111, 116, 111, 110, 105, 99, 32, 102, 117, 110, 99, 116, 105, 111, 110, 10, 96, 96, 96, 10, 111, 112, 97, 113, 117, 101, 32, 102, 32, 58, 32, 78, 97, 116, 32, 226, 134, 146, 32, 78, 97, 116, 10, 97, 120, 105, 111, 109, 32, 102, 77, 111, 110, 111, 32, 58, 32, 120, 32, 226, 137, 164, 32, 121, 32, 226, 134, 146, 32, 102, 32, 120, 32, 226, 137, 164, 32, 102, 32, 121, 10, 96, 96, 96, 10, 97, 110, 100, 32, 121, 111, 117, 32, 119, 97, 110, 116, 32, 116, 111, 32, 105, 110, 115, 116, 114, 117, 99, 116, 32, 96, 103, 114, 105, 110, 100, 96, 32, 116, 111, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 96, 102, 77, 111, 110, 111, 96, 32, 102, 111, 114, 32, 101, 118, 101, 114, 121, 32, 112, 97, 105, 114, 32, 111, 102, 32, 116, 101, 114, 109, 115, 32, 96, 102, 32, 120, 96, 32, 97, 110, 100, 32, 96, 102, 32, 121, 96, 32, 119, 104, 101, 110, 10, 96, 120, 32, 226, 137, 164, 32, 121, 96, 32, 97, 110, 100, 32, 96, 120, 96, 32, 105, 115, 32, 42, 42, 110, 111, 116, 42, 42, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 96, 121, 96, 46, 32, 89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 10, 96, 96, 96, 10, 103, 114, 105, 110, 100, 95, 112, 97, 116, 116, 101, 114, 110, 32, 102, 77, 111, 110, 111, 32, 61, 62, 32, 102, 32, 120, 44, 32, 102, 32, 121, 32, 119, 104, 101, 114, 101, 10, 32, 32, 103, 117, 97, 114, 100, 32, 120, 32, 226, 137, 164, 32, 121, 10, 32, 32, 120, 32, 61, 47, 61, 32, 121, 10, 96, 96, 96, 10, 84, 104, 101, 110, 44, 32, 105, 110, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 101, 120, 97, 109, 112, 108, 101, 44, 32, 111, 110, 108, 121, 32, 116, 104, 114, 101, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 97, 114, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 46, 10, 96, 96, 96, 10, 47, 45, 45, 10, 116, 114, 97, 99, 101, 58, 32, 91, 103, 114, 105, 110, 100, 46, 101, 109, 97, 116, 99, 104, 46, 105, 110, 115, 116, 97, 110, 99, 101, 93, 32, 102, 77, 111, 110, 111, 58, 32, 97, 32, 226, 137, 164, 32, 102, 32, 97, 32, 226, 134, 146, 32, 102, 32, 97, 32, 226, 137, 164, 32, 102, 32, 40, 102, 32, 97, 41, 10, 91, 103, 114, 105, 110, 100, 46, 101, 109, 97, 116, 99, 104, 46, 105, 110, 115, 116, 97, 110, 99, 101, 93, 32, 102, 77, 111, 110, 111, 58, 32, 102, 32, 97, 32, 226, 137, 164, 32, 102, 32, 40, 102, 32, 97, 41, 32, 226, 134, 146, 32, 102, 32, 40, 102, 32, 97, 41, 32, 226, 137, 164, 32, 102, 32, 40, 102, 32, 40, 102, 32, 97, 41, 41, 10, 91, 103, 114, 105, 110, 100, 46, 101, 109, 97, 116, 99, 104, 46, 105, 110, 115, 116, 97, 110, 99, 101, 93, 32, 102, 77, 111, 110, 111, 58, 32, 97, 32, 226, 137, 164, 32, 102, 32, 40, 102, 32, 97, 41, 32, 226, 134, 146, 32, 102, 32, 97, 32, 226, 137, 164, 32, 102, 32, 40, 102, 32, 40, 102, 32, 97, 41, 41, 10, 45, 47, 10, 35, 103, 117, 97, 114, 100, 95, 109, 115, 103, 115, 32, 105, 110, 10, 101, 120, 97, 109, 112, 108, 101, 32, 58, 32, 102, 32, 98, 32, 61, 32, 102, 32, 99, 32, 226, 134, 146, 32, 97, 32, 226, 137, 164, 32, 102, 32, 97, 32, 226, 134, 146, 32, 102, 32, 40, 102, 32, 97, 41, 32, 226, 137, 164, 32, 102, 32, 40, 102, 32, 40, 102, 32, 97, 41, 41, 32, 58, 61, 32, 98, 121, 10, 32, 32, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 116, 114, 97, 99, 101, 46, 103, 114, 105, 110, 100, 46, 101, 109, 97, 116, 99, 104, 46, 105, 110, 115, 116, 97, 110, 99, 101, 32, 116, 114, 117, 101, 32, 105, 110, 10, 32, 32, 103, 114, 105, 110, 100, 10, 96, 96, 96, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__7_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_ident_formatter___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_optional_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value) as *mut crate::leanh::LeanObject,67484279027498894 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,15509248667393904559 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value) as *mut crate::leanh::LeanObject,1634303821783410512 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,1951216414190038513 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value) as *mut crate::leanh::LeanObject,358054841606714373 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,17730510928870966040 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value) as *mut crate::leanh::LeanObject,6009541856878394148 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,8679582806905632013 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value) as *mut crate::leanh::LeanObject,12776886811539497825 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,8601424120598036236 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_numLit_formatter___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__4_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__7_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value) as *mut crate::leanh::LeanObject,10564253717456944082 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,18037465003973108379 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value) as *mut crate::leanh::LeanObject,816581574741003704 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,16443028428162014441 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value) as *mut crate::leanh::LeanObject,3440059094326707764 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,12020587824553360061 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value) as *mut crate::leanh::LeanObject,1572271875277745300 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,17166768888271290589 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_termParser_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value) as *mut crate::leanh::LeanObject,5471431434235198435 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,2235381351994204086 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__0_value) as *mut crate::leanh::LeanObject,16996207256393601998 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,9376574462899831023 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_atomic_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value) as *mut crate::leanh::LeanObject,12235799381117781943 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,6536687254894636754 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_atomic_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value) as *mut crate::leanh::LeanObject,12510525609298890846 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,13087045441266348831 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value) as *mut crate::leanh::LeanObject,2874757003574178313 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,7739730227165469380 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_Term_attrKind_formatter___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__7_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_optional_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__8_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_darrow_formatter___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__9_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_formatter___closed__10_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_sepBy1_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__9_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_formatter___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_formatter___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__0_value) as *mut crate::leanh::LeanObject,2214494411411724007 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,10691271201312786530 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__7_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_ident_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_optional_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__4_value) as *mut crate::leanh::LeanObject,67484279027498894 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,1899522355600184523 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0_value) as *mut crate::leanh::LeanObject,1634303821783410512 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,2396558474787859861 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__0_value) as *mut crate::leanh::LeanObject,358054841606714373 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,2275652074281228260 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0_value) as *mut crate::leanh::LeanObject,6009541856878394148 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,12092338042384664857 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__0_value) as *mut crate::leanh::LeanObject,12776886811539497825 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,1318287746476407792 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_numLit_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__4_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__7_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0_value) as *mut crate::leanh::LeanObject,10564253717456944082 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,15804523955345264447 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0_value) as *mut crate::leanh::LeanObject,816581574741003704 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,13024283192310369949 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__0_value) as *mut crate::leanh::LeanObject,3440059094326707764 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,17798142534307700937 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0_value) as *mut crate::leanh::LeanObject,1572271875277745300 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,10210765369642298025 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_termParser_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__4_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard___closed__0_value) as *mut crate::leanh::LeanObject,5471431434235198435 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,5470959371804881306 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_check___closed__0_value) as *mut crate::leanh::LeanObject,16996207256393601998 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,7372412592061600651 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0_value) as *mut crate::leanh::LeanObject,12235799381117781943 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,158082561384562654 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__3_value) as *mut crate::leanh::LeanObject,7587423409180122123 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__0_value) as *mut crate::leanh::LeanObject,12510525609298890846 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,15954706680443793083 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_ppLine_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_grindPatternCnstrs___closed__0_value) as *mut crate::leanh::LeanObject,2874757003574178313 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,14388158382142931000 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_Term_attrKind_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_optional_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_darrow_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__9_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_sepBy1_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__9_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_grindPattern___closed__0_value) as *mut crate::leanh::LeanObject,2214494411411724007 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,5394955685623265518 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm___closed__0_value: crate::leanh::LeanStringObject<
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
        105, 110, 105, 116, 71, 114, 105, 110, 100, 78, 111, 114, 109, 0,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_initGrindNorm___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2751463752799107324 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_initGrindNorm___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_initGrindNorm___closed__3_value: crate::leanh::LeanStringObject<
    17,
> = crate::leanh::LeanStringObject {
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
        105, 110, 105, 116, 95, 103, 114, 105, 110, 100, 95, 110, 111, 114, 109, 32, 0,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_initGrindNorm___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_initGrindNorm___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_initGrindNorm___closed__6_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Parser_Command_initGrindNorm___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Command_initGrindNorm___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_initGrindNorm___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_initGrindNorm___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_initGrindNorm___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_initGrindNorm___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_initGrindNorm___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Command_initGrindNorm___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Command_initGrindNorm___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Command_initGrindNorm: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Command_initGrindNorm_formatter___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_formatter___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_formatter___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_many_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Command_initGrindNorm_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_formatter___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_formatter___closed__4_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_formatter___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_formatter___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_formatter___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_formatter___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_formatter___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_formatter___closed__7_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_formatter___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_formatter___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__0_value) as *mut crate::leanh::LeanObject,2751463752799107324 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,9295157913782381269 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_many_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__3_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__4_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__6_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__2_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_initGrindNorm___closed__0_value) as *mut crate::leanh::LeanObject,2751463752799107324 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__0_value) as *mut crate::leanh::LeanObject,2381228066784469169 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2423_: u8 = 0;
    let mut v___x_2424_: u8 = 0;
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = 0;
    v___x_2424_ = 1;
    v___x_2425_ = l_Lean_Parser_Command_GrindCnstr_isValue___closed__5;
    v___x_2426_ = l_Lean_Parser_Command_GrindCnstr_isValue___closed__4;
    v___x_2427_ = l_Lean_Parser_mkAntiquot(v___x_2426_, v___x_2425_, v___x_2424_, v___x_2423_);
    return v___x_2427_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = 0;
    v___x_2430_ = l_Lean_Parser_Command_GrindCnstr_isValue___closed__7;
    v___x_2431_ = l_Lean_Parser_nonReservedSymbol(v___x_2430_, v___x_2429_);
    return v___x_2431_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = l_Lean_Parser_Command_GrindCnstr_isValue___closed__9;
    v___x_2434_ = l_Lean_Parser_symbol(v___x_2433_);
    return v___x_2434_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__10_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__10,
    );
    v___x_2436_ = l_Lean_Parser_optional(v___x_2435_);
    return v___x_2436_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__11_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__11,
    );
    v___x_2438_ = l_Lean_Parser_ident;
    v___x_2439_ = l_Lean_Parser_andthen(v___x_2438_, v___x_2437_);
    return v___x_2439_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2440_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12,
    );
    v___x_2441_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__8,
    );
    v___x_2442_ = l_Lean_Parser_andthen(v___x_2441_, v___x_2440_);
    return v___x_2442_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__13_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__13,
    );
    v___x_2444_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2445_ = l_Lean_Parser_Command_GrindCnstr_isValue___closed__5;
    v___x_2446_ = l_Lean_Parser_leadingNode(v___x_2445_, v___x_2444_, v___x_2443_);
    return v___x_2446_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__14_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__14,
    );
    v___x_2448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__6,
    );
    v___x_2449_ = l_Lean_Parser_withAntiquot(v___x_2448_, v___x_2447_);
    return v___x_2449_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__15_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__15,
    );
    v___x_2451_ = l_Lean_Parser_Command_GrindCnstr_isValue___closed__5;
    v___x_2452_ = l_Lean_Parser_withCache(v___x_2451_, v___x_2450_);
    return v___x_2452_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isValue() -> *mut crate::leanh::LeanObject {
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2453_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__16_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__16,
    );
    return v___x_2453_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = 0;
    v___x_2462_ = 1;
    v___x_2463_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1;
    v___x_2464_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__0;
    v___x_2465_ = l_Lean_Parser_mkAntiquot(v___x_2464_, v___x_2463_, v___x_2462_, v___x_2461_);
    return v___x_2465_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2467_: u8 = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2467_ = 0;
    v___x_2468_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__3;
    v___x_2469_ = l_Lean_Parser_nonReservedSymbol(v___x_2468_, v___x_2467_);
    return v___x_2469_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12,
    );
    v___x_2471_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__4,
    );
    v___x_2472_ = l_Lean_Parser_andthen(v___x_2471_, v___x_2470_);
    return v___x_2472_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__5,
    );
    v___x_2474_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2475_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1;
    v___x_2476_ = l_Lean_Parser_leadingNode(v___x_2475_, v___x_2474_, v___x_2473_);
    return v___x_2476_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__6,
    );
    v___x_2478_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__2,
    );
    v___x_2479_ = l_Lean_Parser_withAntiquot(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__7,
    );
    v___x_2481_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1;
    v___x_2482_ = l_Lean_Parser_withCache(v___x_2481_, v___x_2480_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__8,
    );
    return v___x_2483_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ = 0;
    v___x_2492_ = 1;
    v___x_2493_ = l_Lean_Parser_Command_GrindCnstr_notValue___closed__1;
    v___x_2494_ = l_Lean_Parser_Command_GrindCnstr_notValue___closed__0;
    v___x_2495_ = l_Lean_Parser_mkAntiquot(v___x_2494_, v___x_2493_, v___x_2492_, v___x_2491_);
    return v___x_2495_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2497_: u8 = 0;
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = 0;
    v___x_2498_ = l_Lean_Parser_Command_GrindCnstr_notValue___closed__3;
    v___x_2499_ = l_Lean_Parser_nonReservedSymbol(v___x_2498_, v___x_2497_);
    return v___x_2499_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2500_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12,
    );
    v___x_2501_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__4,
    );
    v___x_2502_ = l_Lean_Parser_andthen(v___x_2501_, v___x_2500_);
    return v___x_2502_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2503_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__5,
    );
    v___x_2504_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2505_ = l_Lean_Parser_Command_GrindCnstr_notValue___closed__1;
    v___x_2506_ = l_Lean_Parser_leadingNode(v___x_2505_, v___x_2504_, v___x_2503_);
    return v___x_2506_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__6,
    );
    v___x_2508_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__2,
    );
    v___x_2509_ = l_Lean_Parser_withAntiquot(v___x_2508_, v___x_2507_);
    return v___x_2509_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__7,
    );
    v___x_2511_ = l_Lean_Parser_Command_GrindCnstr_notValue___closed__1;
    v___x_2512_ = l_Lean_Parser_withCache(v___x_2511_, v___x_2510_);
    return v___x_2512_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notValue() -> *mut crate::leanh::LeanObject {
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2513_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notValue___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notValue___closed__8,
    );
    return v___x_2513_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2521_: u8 = 0;
    let mut v___x_2522_: u8 = 0;
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = 0;
    v___x_2522_ = 1;
    v___x_2523_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1;
    v___x_2524_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__0;
    v___x_2525_ = l_Lean_Parser_mkAntiquot(v___x_2524_, v___x_2523_, v___x_2522_, v___x_2521_);
    return v___x_2525_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = 0;
    v___x_2528_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__3;
    v___x_2529_ = l_Lean_Parser_nonReservedSymbol(v___x_2528_, v___x_2527_);
    return v___x_2529_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12,
    );
    v___x_2531_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__4,
    );
    v___x_2532_ = l_Lean_Parser_andthen(v___x_2531_, v___x_2530_);
    return v___x_2532_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__5,
    );
    v___x_2534_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2535_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1;
    v___x_2536_ = l_Lean_Parser_leadingNode(v___x_2535_, v___x_2534_, v___x_2533_);
    return v___x_2536_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2537_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__6,
    );
    v___x_2538_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__2,
    );
    v___x_2539_ = l_Lean_Parser_withAntiquot(v___x_2538_, v___x_2537_);
    return v___x_2539_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2540_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__7,
    );
    v___x_2541_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1;
    v___x_2542_ = l_Lean_Parser_withCache(v___x_2541_, v___x_2540_);
    return v___x_2542_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2543_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__8,
    );
    return v___x_2543_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2551_ = 0;
    v___x_2552_ = 1;
    v___x_2553_ = l_Lean_Parser_Command_GrindCnstr_isGround___closed__1;
    v___x_2554_ = l_Lean_Parser_Command_GrindCnstr_isGround___closed__0;
    v___x_2555_ = l_Lean_Parser_mkAntiquot(v___x_2554_, v___x_2553_, v___x_2552_, v___x_2551_);
    return v___x_2555_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2557_: u8 = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2557_ = 0;
    v___x_2558_ = l_Lean_Parser_Command_GrindCnstr_isGround___closed__3;
    v___x_2559_ = l_Lean_Parser_nonReservedSymbol(v___x_2558_, v___x_2557_);
    return v___x_2559_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2560_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__12_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__12,
    );
    v___x_2561_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__4,
    );
    v___x_2562_ = l_Lean_Parser_andthen(v___x_2561_, v___x_2560_);
    return v___x_2562_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2563_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__5,
    );
    v___x_2564_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2565_ = l_Lean_Parser_Command_GrindCnstr_isGround___closed__1;
    v___x_2566_ = l_Lean_Parser_leadingNode(v___x_2565_, v___x_2564_, v___x_2563_);
    return v___x_2566_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2567_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__6,
    );
    v___x_2568_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__2,
    );
    v___x_2569_ = l_Lean_Parser_withAntiquot(v___x_2568_, v___x_2567_);
    return v___x_2569_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__7,
    );
    v___x_2571_ = l_Lean_Parser_Command_GrindCnstr_isGround___closed__1;
    v___x_2572_ = l_Lean_Parser_withCache(v___x_2571_, v___x_2570_);
    return v___x_2572_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_isGround() -> *mut crate::leanh::LeanObject {
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isGround___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isGround___closed__8,
    );
    return v___x_2573_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2581_ = 0;
    v___x_2582_ = 1;
    v___x_2583_ = l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1;
    v___x_2584_ = l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__0;
    v___x_2585_ = l_Lean_Parser_mkAntiquot(v___x_2584_, v___x_2583_, v___x_2582_, v___x_2581_);
    return v___x_2585_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2587_: u8 = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = 0;
    v___x_2588_ = l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__3;
    v___x_2589_ = l_Lean_Parser_nonReservedSymbol(v___x_2588_, v___x_2587_);
    return v___x_2589_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2591_ = l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__5;
    v___x_2592_ = l_Lean_Parser_symbol(v___x_2591_);
    return v___x_2592_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__11_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__11,
    );
    v___x_2594_ = l_Lean_Parser_numLit;
    v___x_2595_ = l_Lean_Parser_andthen(v___x_2594_, v___x_2593_);
    return v___x_2595_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2596_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__7,
    );
    v___x_2597_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__6,
    );
    v___x_2598_ = l_Lean_Parser_andthen(v___x_2597_, v___x_2596_);
    return v___x_2598_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2599_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8,
    );
    v___x_2600_ = l_Lean_Parser_ident;
    v___x_2601_ = l_Lean_Parser_andthen(v___x_2600_, v___x_2599_);
    return v___x_2601_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2602_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9,
    );
    v___x_2603_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__4,
    );
    v___x_2604_ = l_Lean_Parser_andthen(v___x_2603_, v___x_2602_);
    return v___x_2604_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2605_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__10,
    );
    v___x_2606_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2607_ = l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1;
    v___x_2608_ = l_Lean_Parser_leadingNode(v___x_2607_, v___x_2606_, v___x_2605_);
    return v___x_2608_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__11,
    );
    v___x_2610_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__2,
    );
    v___x_2611_ = l_Lean_Parser_withAntiquot(v___x_2610_, v___x_2609_);
    return v___x_2611_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__12,
    );
    v___x_2613_ = l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1;
    v___x_2614_ = l_Lean_Parser_withCache(v___x_2613_, v___x_2612_);
    return v___x_2614_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_sizeLt() -> *mut crate::leanh::LeanObject {
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2615_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__13,
    );
    return v___x_2615_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: u8 = 0;
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2623_ = 0;
    v___x_2624_ = 1;
    v___x_2625_ = l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1;
    v___x_2626_ = l_Lean_Parser_Command_GrindCnstr_depthLt___closed__0;
    v___x_2627_ = l_Lean_Parser_mkAntiquot(v___x_2626_, v___x_2625_, v___x_2624_, v___x_2623_);
    return v___x_2627_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = 0;
    v___x_2630_ = l_Lean_Parser_Command_GrindCnstr_depthLt___closed__3;
    v___x_2631_ = l_Lean_Parser_nonReservedSymbol(v___x_2630_, v___x_2629_);
    return v___x_2631_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2632_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__9,
    );
    v___x_2633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__4,
    );
    v___x_2634_ = l_Lean_Parser_andthen(v___x_2633_, v___x_2632_);
    return v___x_2634_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2635_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__5,
    );
    v___x_2636_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2637_ = l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1;
    v___x_2638_ = l_Lean_Parser_leadingNode(v___x_2637_, v___x_2636_, v___x_2635_);
    return v___x_2638_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__6,
    );
    v___x_2640_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__2,
    );
    v___x_2641_ = l_Lean_Parser_withAntiquot(v___x_2640_, v___x_2639_);
    return v___x_2641_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__7,
    );
    v___x_2643_ = l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1;
    v___x_2644_ = l_Lean_Parser_withCache(v___x_2643_, v___x_2642_);
    return v___x_2644_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_depthLt() -> *mut crate::leanh::LeanObject {
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_depthLt___closed__8,
    );
    return v___x_2645_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2653_: u8 = 0;
    let mut v___x_2654_: u8 = 0;
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2653_ = 0;
    v___x_2654_ = 1;
    v___x_2655_ = l_Lean_Parser_Command_GrindCnstr_genLt___closed__1;
    v___x_2656_ = l_Lean_Parser_Command_GrindCnstr_genLt___closed__0;
    v___x_2657_ = l_Lean_Parser_mkAntiquot(v___x_2656_, v___x_2655_, v___x_2654_, v___x_2653_);
    return v___x_2657_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2659_: u8 = 0;
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = 0;
    v___x_2660_ = l_Lean_Parser_Command_GrindCnstr_genLt___closed__3;
    v___x_2661_ = l_Lean_Parser_nonReservedSymbol(v___x_2660_, v___x_2659_);
    return v___x_2661_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2662_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8,
    );
    v___x_2663_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__4,
    );
    v___x_2664_ = l_Lean_Parser_andthen(v___x_2663_, v___x_2662_);
    return v___x_2664_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__5,
    );
    v___x_2666_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2667_ = l_Lean_Parser_Command_GrindCnstr_genLt___closed__1;
    v___x_2668_ = l_Lean_Parser_leadingNode(v___x_2667_, v___x_2666_, v___x_2665_);
    return v___x_2668_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2669_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__6,
    );
    v___x_2670_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__2,
    );
    v___x_2671_ = l_Lean_Parser_withAntiquot(v___x_2670_, v___x_2669_);
    return v___x_2671_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2672_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__7,
    );
    v___x_2673_ = l_Lean_Parser_Command_GrindCnstr_genLt___closed__1;
    v___x_2674_ = l_Lean_Parser_withCache(v___x_2673_, v___x_2672_);
    return v___x_2674_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_genLt() -> *mut crate::leanh::LeanObject {
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2675_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_genLt___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_genLt___closed__8,
    );
    return v___x_2675_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = 0;
    v___x_2684_ = 1;
    v___x_2685_ = l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1;
    v___x_2686_ = l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__0;
    v___x_2687_ = l_Lean_Parser_mkAntiquot(v___x_2686_, v___x_2685_, v___x_2684_, v___x_2683_);
    return v___x_2687_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2689_: u8 = 0;
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2689_ = 0;
    v___x_2690_ = l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__3;
    v___x_2691_ = l_Lean_Parser_nonReservedSymbol(v___x_2690_, v___x_2689_);
    return v___x_2691_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2692_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__8,
    );
    v___x_2693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__4,
    );
    v___x_2694_ = l_Lean_Parser_andthen(v___x_2693_, v___x_2692_);
    return v___x_2694_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2695_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__5,
    );
    v___x_2696_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2697_ = l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1;
    v___x_2698_ = l_Lean_Parser_leadingNode(v___x_2697_, v___x_2696_, v___x_2695_);
    return v___x_2698_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__6,
    );
    v___x_2700_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__2,
    );
    v___x_2701_ = l_Lean_Parser_withAntiquot(v___x_2700_, v___x_2699_);
    return v___x_2701_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__7,
    );
    v___x_2703_ = l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1;
    v___x_2704_ = l_Lean_Parser_withCache(v___x_2703_, v___x_2702_);
    return v___x_2704_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_maxInsts() -> *mut crate::leanh::LeanObject {
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__8,
    );
    return v___x_2705_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2713_: u8 = 0;
    let mut v___x_2714_: u8 = 0;
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2713_ = 0;
    v___x_2714_ = 1;
    v___x_2715_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__1;
    v___x_2716_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__0;
    v___x_2717_ = l_Lean_Parser_mkAntiquot(v___x_2716_, v___x_2715_, v___x_2714_, v___x_2713_);
    return v___x_2717_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2719_: u8 = 0;
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2719_ = 0;
    v___x_2720_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__3;
    v___x_2721_ = l_Lean_Parser_nonReservedSymbol(v___x_2720_, v___x_2719_);
    return v___x_2721_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__5;
    v___x_2724_ = l_Lean_Parser_checkColGe(v___x_2723_);
    return v___x_2724_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2726_ = l_Lean_Parser_termParser(v___x_2725_);
    return v___x_2726_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2727_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_isValue___closed__11_once),
        _init_l_Lean_Parser_Command_GrindCnstr_isValue___closed__11,
    );
    v___x_2728_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__7,
    );
    v___x_2729_ = l_Lean_Parser_andthen(v___x_2728_, v___x_2727_);
    return v___x_2729_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__8,
    );
    v___x_2731_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__6,
    );
    v___x_2732_ = l_Lean_Parser_andthen(v___x_2731_, v___x_2730_);
    return v___x_2732_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9,
    );
    v___x_2734_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__4,
    );
    v___x_2735_ = l_Lean_Parser_andthen(v___x_2734_, v___x_2733_);
    return v___x_2735_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2736_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__10_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__10,
    );
    v___x_2737_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2738_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__1;
    v___x_2739_ = l_Lean_Parser_leadingNode(v___x_2738_, v___x_2737_, v___x_2736_);
    return v___x_2739_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2740_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__11_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__11,
    );
    v___x_2741_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__2,
    );
    v___x_2742_ = l_Lean_Parser_withAntiquot(v___x_2741_, v___x_2740_);
    return v___x_2742_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2743_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__12_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__12,
    );
    v___x_2744_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__1;
    v___x_2745_ = l_Lean_Parser_withCache(v___x_2744_, v___x_2743_);
    return v___x_2745_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard() -> *mut crate::leanh::LeanObject {
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2746_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__13_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__13,
    );
    return v___x_2746_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2754_: u8 = 0;
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = 0;
    v___x_2755_ = 1;
    v___x_2756_ = l_Lean_Parser_Command_GrindCnstr_check___closed__1;
    v___x_2757_ = l_Lean_Parser_Command_GrindCnstr_check___closed__0;
    v___x_2758_ = l_Lean_Parser_mkAntiquot(v___x_2757_, v___x_2756_, v___x_2755_, v___x_2754_);
    return v___x_2758_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2760_ = 0;
    v___x_2761_ = l_Lean_Parser_Command_GrindCnstr_check___closed__3;
    v___x_2762_ = l_Lean_Parser_nonReservedSymbol(v___x_2761_, v___x_2760_);
    return v___x_2762_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9,
    );
    v___x_2764_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_check___closed__4,
    );
    v___x_2765_ = l_Lean_Parser_andthen(v___x_2764_, v___x_2763_);
    return v___x_2765_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2766_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_check___closed__5,
    );
    v___x_2767_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2768_ = l_Lean_Parser_Command_GrindCnstr_check___closed__1;
    v___x_2769_ = l_Lean_Parser_leadingNode(v___x_2768_, v___x_2767_, v___x_2766_);
    return v___x_2769_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_check___closed__6,
    );
    v___x_2771_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_check___closed__2,
    );
    v___x_2772_ = l_Lean_Parser_withAntiquot(v___x_2771_, v___x_2770_);
    return v___x_2772_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2773_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_check___closed__7,
    );
    v___x_2774_ = l_Lean_Parser_Command_GrindCnstr_check___closed__1;
    v___x_2775_ = l_Lean_Parser_withCache(v___x_2774_, v___x_2773_);
    return v___x_2775_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check() -> *mut crate::leanh::LeanObject {
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_check___closed__8,
    );
    return v___x_2776_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2784_: u8 = 0;
    let mut v___x_2785_: u8 = 0;
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2784_ = 0;
    v___x_2785_ = 1;
    v___x_2786_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1;
    v___x_2787_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__0;
    v___x_2788_ = l_Lean_Parser_mkAntiquot(v___x_2787_, v___x_2786_, v___x_2785_, v___x_2784_);
    return v___x_2788_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2790_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__3;
    v___x_2791_ = l_Lean_Parser_symbol(v___x_2790_);
    return v___x_2791_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__4,
    );
    v___x_2793_ = l_Lean_Parser_ident;
    v___x_2794_ = l_Lean_Parser_andthen(v___x_2793_, v___x_2792_);
    return v___x_2794_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2795_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__5,
    );
    v___x_2796_ = l_Lean_Parser_atomic(v___x_2795_);
    return v___x_2796_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2797_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9,
    );
    v___x_2798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__6,
    );
    v___x_2799_ = l_Lean_Parser_andthen(v___x_2798_, v___x_2797_);
    return v___x_2799_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__7,
    );
    v___x_2801_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2802_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1;
    v___x_2803_ = l_Lean_Parser_leadingNode(v___x_2802_, v___x_2801_, v___x_2800_);
    return v___x_2803_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2804_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__8,
    );
    v___x_2805_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__2,
    );
    v___x_2806_ = l_Lean_Parser_withAntiquot(v___x_2805_, v___x_2804_);
    return v___x_2806_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2807_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__9,
    );
    v___x_2808_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1;
    v___x_2809_ = l_Lean_Parser_withCache(v___x_2808_, v___x_2807_);
    return v___x_2809_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq() -> *mut crate::leanh::LeanObject {
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2810_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10_once),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__10,
    );
    return v___x_2810_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2818_: u8 = 0;
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2818_ = 0;
    v___x_2819_ = 1;
    v___x_2820_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__1;
    v___x_2821_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__0;
    v___x_2822_ = l_Lean_Parser_mkAntiquot(v___x_2821_, v___x_2820_, v___x_2819_, v___x_2818_);
    return v___x_2822_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__3;
    v___x_2825_ = l_Lean_Parser_symbol(v___x_2824_);
    return v___x_2825_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2826_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__4,
    );
    v___x_2827_ = l_Lean_Parser_ident;
    v___x_2828_ = l_Lean_Parser_andthen(v___x_2827_, v___x_2826_);
    return v___x_2828_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2829_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__5,
    );
    v___x_2830_ = l_Lean_Parser_atomic(v___x_2829_);
    return v___x_2830_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__9_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__9,
    );
    v___x_2832_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__6,
    );
    v___x_2833_ = l_Lean_Parser_andthen(v___x_2832_, v___x_2831_);
    return v___x_2833_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2834_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__7,
    );
    v___x_2835_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2836_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__1;
    v___x_2837_ = l_Lean_Parser_leadingNode(v___x_2836_, v___x_2835_, v___x_2834_);
    return v___x_2837_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2838_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__8_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__8,
    );
    v___x_2839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__2,
    );
    v___x_2840_ = l_Lean_Parser_withAntiquot(v___x_2839_, v___x_2838_);
    return v___x_2840_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__9_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__9,
    );
    v___x_2842_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__1;
    v___x_2843_ = l_Lean_Parser_withCache(v___x_2842_, v___x_2841_);
    return v___x_2843_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq() -> *mut crate::leanh::LeanObject {
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq___closed__10_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq___closed__10,
    );
    return v___x_2844_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2845_ = l_Lean_Parser_Command_GrindCnstr_defEq;
    v___x_2846_ = l_Lean_Parser_Command_GrindCnstr_notDefEq;
    v___x_2847_ = l_Lean_Parser_orelse(v___x_2846_, v___x_2845_);
    return v___x_2847_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2848_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__0_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__0,
    );
    v___x_2849_ = l_Lean_Parser_Command_GrindCnstr_check;
    v___x_2850_ = l_Lean_Parser_orelse(v___x_2849_, v___x_2848_);
    return v___x_2850_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2851_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__1_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__1,
    );
    v___x_2852_ = l_Lean_Parser_Command_GrindCnstr_guard;
    v___x_2853_ = l_Lean_Parser_orelse(v___x_2852_, v___x_2851_);
    return v___x_2853_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2854_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__2_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__2,
    );
    v___x_2855_ = l_Lean_Parser_Command_GrindCnstr_maxInsts;
    v___x_2856_ = l_Lean_Parser_orelse(v___x_2855_, v___x_2854_);
    return v___x_2856_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2857_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__3_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__3,
    );
    v___x_2858_ = l_Lean_Parser_Command_GrindCnstr_genLt;
    v___x_2859_ = l_Lean_Parser_orelse(v___x_2858_, v___x_2857_);
    return v___x_2859_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2860_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__4_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__4,
    );
    v___x_2861_ = l_Lean_Parser_Command_GrindCnstr_depthLt;
    v___x_2862_ = l_Lean_Parser_orelse(v___x_2861_, v___x_2860_);
    return v___x_2862_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2863_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__5_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__5,
    );
    v___x_2864_ = l_Lean_Parser_Command_GrindCnstr_sizeLt;
    v___x_2865_ = l_Lean_Parser_orelse(v___x_2864_, v___x_2863_);
    return v___x_2865_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2866_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__6_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__6,
    );
    v___x_2867_ = l_Lean_Parser_Command_GrindCnstr_isGround;
    v___x_2868_ = l_Lean_Parser_orelse(v___x_2867_, v___x_2866_);
    return v___x_2868_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__7_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__7,
    );
    v___x_2870_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue;
    v___x_2871_ = l_Lean_Parser_orelse(v___x_2870_, v___x_2869_);
    return v___x_2871_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__8_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__8,
    );
    v___x_2873_ = l_Lean_Parser_Command_GrindCnstr_notValue;
    v___x_2874_ = l_Lean_Parser_orelse(v___x_2873_, v___x_2872_);
    return v___x_2874_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__9_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__9,
    );
    v___x_2876_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue;
    v___x_2877_ = l_Lean_Parser_orelse(v___x_2876_, v___x_2875_);
    return v___x_2877_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2878_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__10_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__10,
    );
    v___x_2879_ = l_Lean_Parser_Command_GrindCnstr_isValue;
    v___x_2880_ = l_Lean_Parser_orelse(v___x_2879_, v___x_2878_);
    return v___x_2880_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr() -> *mut crate::leanh::LeanObject {
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2881_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr___closed__11_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr___closed__11,
    );
    return v___x_2881_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2888_ = 0;
    v___x_2889_ = 1;
    v___x_2890_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__1;
    v___x_2891_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__0;
    v___x_2892_ = l_Lean_Parser_mkAntiquot(v___x_2891_, v___x_2890_, v___x_2889_, v___x_2888_);
    return v___x_2892_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2894_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__3;
    v___x_2895_ = l_Lean_Parser_symbol(v___x_2894_);
    return v___x_2895_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lean_Parser_Command_grindPatternCnstr;
    v___x_2897_ = l_Lean_Parser_skip;
    v___x_2898_ = l_Lean_Parser_andthen(v___x_2897_, v___x_2896_);
    return v___x_2898_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2899_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__5_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__5,
    );
    v___x_2900_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__6,
    );
    v___x_2901_ = l_Lean_Parser_andthen(v___x_2900_, v___x_2899_);
    return v___x_2901_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__6_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__6,
    );
    v___x_2903_ = l_Lean_Parser_many1(v___x_2902_);
    return v___x_2903_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2904_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__7_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__7,
    );
    v___x_2905_ = l_Lean_Parser_withPosition(v___x_2904_);
    return v___x_2905_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2906_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__8_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__8,
    );
    v___x_2907_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__4_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__4,
    );
    v___x_2908_ = l_Lean_Parser_andthen(v___x_2907_, v___x_2906_);
    return v___x_2908_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2909_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__9_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__9,
    );
    v___x_2910_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2911_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__1;
    v___x_2912_ = l_Lean_Parser_leadingNode(v___x_2911_, v___x_2910_, v___x_2909_);
    return v___x_2912_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__10_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__10,
    );
    v___x_2914_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__2_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__2,
    );
    v___x_2915_ = l_Lean_Parser_withAntiquot(v___x_2914_, v___x_2913_);
    return v___x_2915_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__11_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__11,
    );
    v___x_2917_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__1;
    v___x_2918_ = l_Lean_Parser_withCache(v___x_2917_, v___x_2916_);
    return v___x_2918_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs() -> *mut crate::leanh::LeanObject {
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs___closed__12_once),
        _init_l_Lean_Parser_Command_grindPatternCnstrs___closed__12,
    );
    return v___x_2919_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2926_ = 0;
    v___x_2927_ = 1;
    v___x_2928_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_2929_ = l_Lean_Parser_Command_grindPattern___closed__0;
    v___x_2930_ = l_Lean_Parser_mkAntiquot(v___x_2929_, v___x_2928_, v___x_2927_, v___x_2926_);
    return v___x_2930_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2932_ = l_Lean_Parser_Command_grindPattern___closed__3;
    v___x_2933_ = l_Lean_Parser_symbol(v___x_2932_);
    return v___x_2933_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2935_ = l_Lean_Parser_Command_grindPattern___closed__5;
    v___x_2936_ = l_Lean_Parser_symbol(v___x_2935_);
    return v___x_2936_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2938_ = l_Lean_Parser_Command_grindPattern___closed__7;
    v___x_2939_ = l_Lean_Parser_symbol(v___x_2938_);
    return v___x_2939_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__8_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__8,
    );
    v___x_2941_ = l_Lean_Parser_ident;
    v___x_2942_ = l_Lean_Parser_andthen(v___x_2941_, v___x_2940_);
    return v___x_2942_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2943_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__9_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__9,
    );
    v___x_2944_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__6_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__6,
    );
    v___x_2945_ = l_Lean_Parser_andthen(v___x_2944_, v___x_2943_);
    return v___x_2945_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__10_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__10,
    );
    v___x_2947_ = l_Lean_Parser_optional(v___x_2946_);
    return v___x_2947_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_Parser_Command_grindPattern___closed__12;
    v___x_2950_ = l_Lean_Parser_symbol(v___x_2949_);
    return v___x_2950_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2951_: u8 = 0;
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2951_ = 0;
    v___x_2952_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__13_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__13,
    );
    v___x_2953_ = l_Lean_Parser_Command_grindPattern___closed__12;
    v___x_2954_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard___closed__7_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard___closed__7,
    );
    v___x_2955_ = l_Lean_Parser_sepBy1(v___x_2954_, v___x_2953_, v___x_2952_, v___x_2951_);
    return v___x_2955_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2956_ = l_Lean_Parser_Command_grindPatternCnstrs;
    v___x_2957_ = l_Lean_Parser_optional(v___x_2956_);
    return v___x_2957_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2958_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__15_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__15,
    );
    v___x_2959_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__14_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__14,
    );
    v___x_2960_ = l_Lean_Parser_andthen(v___x_2959_, v___x_2958_);
    return v___x_2960_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2961_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__16_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__16,
    );
    v___x_2962_ = l_Lean_Parser_darrow;
    v___x_2963_ = l_Lean_Parser_andthen(v___x_2962_, v___x_2961_);
    return v___x_2963_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2964_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__17_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__17,
    );
    v___x_2965_ = l_Lean_Parser_ident;
    v___x_2966_ = l_Lean_Parser_andthen(v___x_2965_, v___x_2964_);
    return v___x_2966_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2967_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__18_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__18,
    );
    v___x_2968_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__11_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__11,
    );
    v___x_2969_ = l_Lean_Parser_andthen(v___x_2968_, v___x_2967_);
    return v___x_2969_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2970_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__19_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__19,
    );
    v___x_2971_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__4_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__4,
    );
    v___x_2972_ = l_Lean_Parser_andthen(v___x_2971_, v___x_2970_);
    return v___x_2972_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__20_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__20,
    );
    v___x_2974_ = l_Lean_Parser_Term_attrKind;
    v___x_2975_ = l_Lean_Parser_andthen(v___x_2974_, v___x_2973_);
    return v___x_2975_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__21_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__21,
    );
    v___x_2977_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2978_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_2979_ = l_Lean_Parser_leadingNode(v___x_2978_, v___x_2977_, v___x_2976_);
    return v___x_2979_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2980_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__22_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__22,
    );
    v___x_2981_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__2_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__2,
    );
    v___x_2982_ = l_Lean_Parser_withAntiquot(v___x_2981_, v___x_2980_);
    return v___x_2982_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__23_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__23,
    );
    v___x_2984_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_2985_ = l_Lean_Parser_withCache(v___x_2984_, v___x_2983_);
    return v___x_2985_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern() -> *mut crate::leanh::LeanObject {
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2986_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern___closed__24_once),
        _init_l_Lean_Parser_Command_grindPattern___closed__24,
    );
    return v___x_2986_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2991_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1;
    v___x_2992_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_2993_ = l_Lean_Parser_Command_grindPattern;
    v___x_2994_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_2995_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_2991_, v___x_2992_, v___x_2993_, v___x_2994_);
    return v___x_2995_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___boxed(
    mut v_a_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2997_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1();
    return v_res_2997_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3000_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_3001_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___closed__0;
    v___x_3002_ = l_Lean_addBuiltinDocString(v___x_3000_, v___x_3001_);
    return v___x_3002_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3___boxed(
    mut v_a_3003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3004_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3();
    return v_res_3004_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isValue_formatter(
    mut v_a_3031_: *mut crate::leanh::LeanObject,
    mut v_a_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3036_ = l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__0;
    v___x_3037_ = l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__7;
    v___x_3038_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3036_,
        v___x_3037_,
        v_a_3031_,
        v_a_3032_,
        v_a_3033_,
        v_a_3034_,
    );
    return v___x_3038_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed(
    mut v_a_3039_: *mut crate::leanh::LeanObject,
    mut v_a_3040_: *mut crate::leanh::LeanObject,
    mut v_a_3041_: *mut crate::leanh::LeanObject,
    mut v_a_3042_: *mut crate::leanh::LeanObject,
    mut v_a_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Lean_Parser_Command_GrindCnstr_isValue_formatter(
        v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_,
    );
    crate::leanh::lean_dec(v_a_3042_);
    crate::leanh::lean_dec_ref(v_a_3041_);
    crate::leanh::lean_dec(v_a_3040_);
    crate::leanh::lean_dec_ref(v_a_3039_);
    return v_res_3044_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3054_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3055_ = l_Lean_Parser_Command_GrindCnstr_isValue___closed__5;
    v___x_3056_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___closed__1;
    v___x_3057_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3058_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3054_,
        v___x_3055_,
        v___x_3056_,
        v___x_3057_,
    );
    return v___x_3058_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7___boxed(
    mut v_a_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3060_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7();
    return v_res_3060_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter(
    mut v_a_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3084_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__0;
    v___x_3085_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___closed__3;
    v___x_3086_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3084_,
        v___x_3085_,
        v_a_3079_,
        v_a_3080_,
        v_a_3081_,
        v_a_3082_,
    );
    return v___x_3086_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed(
    mut v_a_3087_: *mut crate::leanh::LeanObject,
    mut v_a_3088_: *mut crate::leanh::LeanObject,
    mut v_a_3089_: *mut crate::leanh::LeanObject,
    mut v_a_3090_: *mut crate::leanh::LeanObject,
    mut v_a_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3092_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter(
        v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_,
    );
    crate::leanh::lean_dec(v_a_3090_);
    crate::leanh::lean_dec_ref(v_a_3089_);
    crate::leanh::lean_dec(v_a_3088_);
    crate::leanh::lean_dec_ref(v_a_3087_);
    return v_res_3092_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3101_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3102_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1;
    v___x_3103_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___closed__0;
    v___x_3104_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3105_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3101_,
        v___x_3102_,
        v___x_3103_,
        v___x_3104_,
    );
    return v___x_3105_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11___boxed(
    mut v_a_3106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3107_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11();
    return v_res_3107_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notValue_formatter(
    mut v_a_3126_: *mut crate::leanh::LeanObject,
    mut v_a_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3131_ = l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__0;
    v___x_3132_ = l_Lean_Parser_Command_GrindCnstr_notValue_formatter___closed__3;
    v___x_3133_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3131_,
        v___x_3132_,
        v_a_3126_,
        v_a_3127_,
        v_a_3128_,
        v_a_3129_,
    );
    return v___x_3133_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed(
    mut v_a_3134_: *mut crate::leanh::LeanObject,
    mut v_a_3135_: *mut crate::leanh::LeanObject,
    mut v_a_3136_: *mut crate::leanh::LeanObject,
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_Lean_Parser_Command_GrindCnstr_notValue_formatter(
        v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_,
    );
    crate::leanh::lean_dec(v_a_3137_);
    crate::leanh::lean_dec_ref(v_a_3136_);
    crate::leanh::lean_dec(v_a_3135_);
    crate::leanh::lean_dec_ref(v_a_3134_);
    return v_res_3139_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3148_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3149_ = l_Lean_Parser_Command_GrindCnstr_notValue___closed__1;
    v___x_3150_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___closed__0;
    v___x_3151_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3152_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3148_,
        v___x_3149_,
        v___x_3150_,
        v___x_3151_,
    );
    return v___x_3152_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15___boxed(
    mut v_a_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3154_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15();
    return v_res_3154_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter(
    mut v_a_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3178_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__0;
    v___x_3179_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___closed__3;
    v___x_3180_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3178_,
        v___x_3179_,
        v_a_3173_,
        v_a_3174_,
        v_a_3175_,
        v_a_3176_,
    );
    return v___x_3180_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed(
    mut v_a_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3186_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter(
        v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_,
    );
    crate::leanh::lean_dec(v_a_3184_);
    crate::leanh::lean_dec_ref(v_a_3183_);
    crate::leanh::lean_dec(v_a_3182_);
    crate::leanh::lean_dec_ref(v_a_3181_);
    return v_res_3186_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3195_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3196_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1;
    v___x_3197_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___closed__0;
    v___x_3198_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3199_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3195_,
        v___x_3196_,
        v___x_3197_,
        v___x_3198_,
    );
    return v___x_3199_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19___boxed(
    mut v_a_3200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3201_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19();
    return v_res_3201_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isGround_formatter(
    mut v_a_3220_: *mut crate::leanh::LeanObject,
    mut v_a_3221_: *mut crate::leanh::LeanObject,
    mut v_a_3222_: *mut crate::leanh::LeanObject,
    mut v_a_3223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3225_ = l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__0;
    v___x_3226_ = l_Lean_Parser_Command_GrindCnstr_isGround_formatter___closed__3;
    v___x_3227_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3225_,
        v___x_3226_,
        v_a_3220_,
        v_a_3221_,
        v_a_3222_,
        v_a_3223_,
    );
    return v___x_3227_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed(
    mut v_a_3228_: *mut crate::leanh::LeanObject,
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
    mut v_a_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3233_ = l_Lean_Parser_Command_GrindCnstr_isGround_formatter(
        v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_,
    );
    crate::leanh::lean_dec(v_a_3231_);
    crate::leanh::lean_dec_ref(v_a_3230_);
    crate::leanh::lean_dec(v_a_3229_);
    crate::leanh::lean_dec_ref(v_a_3228_);
    return v_res_3233_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3243_ = l_Lean_Parser_Command_GrindCnstr_isGround___closed__1;
    v___x_3244_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___closed__0;
    v___x_3245_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3246_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3242_,
        v___x_3243_,
        v___x_3244_,
        v___x_3245_,
    );
    return v___x_3246_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23___boxed(
    mut v_a_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3248_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23();
    return v_res_3248_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter(
    mut v_a_3279_: *mut crate::leanh::LeanObject,
    mut v_a_3280_: *mut crate::leanh::LeanObject,
    mut v_a_3281_: *mut crate::leanh::LeanObject,
    mut v_a_3282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3284_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__0;
    v___x_3285_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___closed__8;
    v___x_3286_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3284_,
        v___x_3285_,
        v_a_3279_,
        v_a_3280_,
        v_a_3281_,
        v_a_3282_,
    );
    return v___x_3286_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed(
    mut v_a_3287_: *mut crate::leanh::LeanObject,
    mut v_a_3288_: *mut crate::leanh::LeanObject,
    mut v_a_3289_: *mut crate::leanh::LeanObject,
    mut v_a_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3292_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter(
        v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_,
    );
    crate::leanh::lean_dec(v_a_3290_);
    crate::leanh::lean_dec_ref(v_a_3289_);
    crate::leanh::lean_dec(v_a_3288_);
    crate::leanh::lean_dec_ref(v_a_3287_);
    return v_res_3292_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3302_ = l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1;
    v___x_3303_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___closed__0;
    v___x_3304_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3305_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3301_,
        v___x_3302_,
        v___x_3303_,
        v___x_3304_,
    );
    return v___x_3305_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27___boxed(
    mut v_a_3306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27();
    return v_res_3307_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_depthLt_formatter(
    mut v_a_3326_: *mut crate::leanh::LeanObject,
    mut v_a_3327_: *mut crate::leanh::LeanObject,
    mut v_a_3328_: *mut crate::leanh::LeanObject,
    mut v_a_3329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3331_ = l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__0;
    v___x_3332_ = l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___closed__3;
    v___x_3333_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3331_,
        v___x_3332_,
        v_a_3326_,
        v_a_3327_,
        v_a_3328_,
        v_a_3329_,
    );
    return v___x_3333_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed(
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3339_ = l_Lean_Parser_Command_GrindCnstr_depthLt_formatter(
        v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_,
    );
    crate::leanh::lean_dec(v_a_3337_);
    crate::leanh::lean_dec_ref(v_a_3336_);
    crate::leanh::lean_dec(v_a_3335_);
    crate::leanh::lean_dec_ref(v_a_3334_);
    return v_res_3339_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3348_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3349_ = l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1;
    v___x_3350_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___closed__0;
    v___x_3351_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3352_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3348_,
        v___x_3349_,
        v___x_3350_,
        v___x_3351_,
    );
    return v___x_3352_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31___boxed(
    mut v_a_3353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3354_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31();
    return v_res_3354_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_genLt_formatter(
    mut v_a_3373_: *mut crate::leanh::LeanObject,
    mut v_a_3374_: *mut crate::leanh::LeanObject,
    mut v_a_3375_: *mut crate::leanh::LeanObject,
    mut v_a_3376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3378_ = l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__0;
    v___x_3379_ = l_Lean_Parser_Command_GrindCnstr_genLt_formatter___closed__3;
    v___x_3380_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3378_,
        v___x_3379_,
        v_a_3373_,
        v_a_3374_,
        v_a_3375_,
        v_a_3376_,
    );
    return v___x_3380_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed(
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_a_3382_: *mut crate::leanh::LeanObject,
    mut v_a_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
    mut v_a_3385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Lean_Parser_Command_GrindCnstr_genLt_formatter(
        v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_,
    );
    crate::leanh::lean_dec(v_a_3384_);
    crate::leanh::lean_dec_ref(v_a_3383_);
    crate::leanh::lean_dec(v_a_3382_);
    crate::leanh::lean_dec_ref(v_a_3381_);
    return v_res_3386_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3395_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3396_ = l_Lean_Parser_Command_GrindCnstr_genLt___closed__1;
    v___x_3397_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___closed__0;
    v___x_3398_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3399_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3395_,
        v___x_3396_,
        v___x_3397_,
        v___x_3398_,
    );
    return v___x_3399_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35___boxed(
    mut v_a_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35();
    return v_res_3401_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter(
    mut v_a_3420_: *mut crate::leanh::LeanObject,
    mut v_a_3421_: *mut crate::leanh::LeanObject,
    mut v_a_3422_: *mut crate::leanh::LeanObject,
    mut v_a_3423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__0;
    v___x_3426_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___closed__3;
    v___x_3427_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3425_,
        v___x_3426_,
        v_a_3420_,
        v_a_3421_,
        v_a_3422_,
        v_a_3423_,
    );
    return v___x_3427_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed(
    mut v_a_3428_: *mut crate::leanh::LeanObject,
    mut v_a_3429_: *mut crate::leanh::LeanObject,
    mut v_a_3430_: *mut crate::leanh::LeanObject,
    mut v_a_3431_: *mut crate::leanh::LeanObject,
    mut v_a_3432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3433_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter(
        v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_,
    );
    crate::leanh::lean_dec(v_a_3431_);
    crate::leanh::lean_dec_ref(v_a_3430_);
    crate::leanh::lean_dec(v_a_3429_);
    crate::leanh::lean_dec_ref(v_a_3428_);
    return v_res_3433_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3442_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3443_ = l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1;
    v___x_3444_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___closed__0;
    v___x_3445_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3446_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3442_,
        v___x_3443_,
        v___x_3444_,
        v___x_3445_,
    );
    return v___x_3446_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39___boxed(
    mut v_a_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39();
    return v_res_3448_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3465_ = l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__3;
    v___x_3466_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3467_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3467_, 0, v___x_3466_);
    crate::leanh::lean_closure_set(v___x_3467_, 1, v___x_3465_);
    return v___x_3467_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3468_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4,
    );
    v___x_3469_ = l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__1;
    v___x_3470_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3470_, 0, v___x_3469_);
    crate::leanh::lean_closure_set(v___x_3470_, 1, v___x_3468_);
    return v___x_3470_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3471_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__5,
    );
    v___x_3472_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3473_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__1;
    v___x_3474_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3474_, 0, v___x_3473_);
    crate::leanh::lean_closure_set(v___x_3474_, 1, v___x_3472_);
    crate::leanh::lean_closure_set(v___x_3474_, 2, v___x_3471_);
    return v___x_3474_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_guard_formatter(
    mut v_a_3475_: *mut crate::leanh::LeanObject,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
    mut v_a_3477_: *mut crate::leanh::LeanObject,
    mut v_a_3478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3480_ = l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__0;
    v___x_3481_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__6,
    );
    v___x_3482_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3480_,
        v___x_3481_,
        v_a_3475_,
        v_a_3476_,
        v_a_3477_,
        v_a_3478_,
    );
    return v___x_3482_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed(
    mut v_a_3483_: *mut crate::leanh::LeanObject,
    mut v_a_3484_: *mut crate::leanh::LeanObject,
    mut v_a_3485_: *mut crate::leanh::LeanObject,
    mut v_a_3486_: *mut crate::leanh::LeanObject,
    mut v_a_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3488_ = l_Lean_Parser_Command_GrindCnstr_guard_formatter(
        v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_,
    );
    crate::leanh::lean_dec(v_a_3486_);
    crate::leanh::lean_dec_ref(v_a_3485_);
    crate::leanh::lean_dec(v_a_3484_);
    crate::leanh::lean_dec_ref(v_a_3483_);
    return v_res_3488_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3497_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3498_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__1;
    v___x_3499_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___closed__0;
    v___x_3500_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3501_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3497_,
        v___x_3498_,
        v___x_3499_,
        v___x_3500_,
    );
    return v___x_3501_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43___boxed(
    mut v_a_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3503_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43();
    return v_res_3503_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3515_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4,
    );
    v___x_3516_ = l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__1;
    v___x_3517_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3517_, 0, v___x_3516_);
    crate::leanh::lean_closure_set(v___x_3517_, 1, v___x_3515_);
    return v___x_3517_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3518_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2_once),
        _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__2,
    );
    v___x_3519_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3520_ = l_Lean_Parser_Command_GrindCnstr_check___closed__1;
    v___x_3521_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3521_, 0, v___x_3520_);
    crate::leanh::lean_closure_set(v___x_3521_, 1, v___x_3519_);
    crate::leanh::lean_closure_set(v___x_3521_, 2, v___x_3518_);
    return v___x_3521_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_check_formatter(
    mut v_a_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3527_ = l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__0;
    v___x_3528_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3_once),
        _init_l_Lean_Parser_Command_GrindCnstr_check_formatter___closed__3,
    );
    v___x_3529_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3527_,
        v___x_3528_,
        v_a_3522_,
        v_a_3523_,
        v_a_3524_,
        v_a_3525_,
    );
    return v___x_3529_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed(
    mut v_a_3530_: *mut crate::leanh::LeanObject,
    mut v_a_3531_: *mut crate::leanh::LeanObject,
    mut v_a_3532_: *mut crate::leanh::LeanObject,
    mut v_a_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3535_ = l_Lean_Parser_Command_GrindCnstr_check_formatter(
        v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_,
    );
    crate::leanh::lean_dec(v_a_3533_);
    crate::leanh::lean_dec_ref(v_a_3532_);
    crate::leanh::lean_dec(v_a_3531_);
    crate::leanh::lean_dec_ref(v_a_3530_);
    return v_res_3535_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3544_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3545_ = l_Lean_Parser_Command_GrindCnstr_check___closed__1;
    v___x_3546_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___closed__0;
    v___x_3547_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3548_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3544_,
        v___x_3545_,
        v___x_3546_,
        v___x_3547_,
    );
    return v___x_3548_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47___boxed(
    mut v_a_3549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3550_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47();
    return v_res_3550_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3565_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4,
    );
    v___x_3566_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__3;
    v___x_3567_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3567_, 0, v___x_3566_);
    crate::leanh::lean_closure_set(v___x_3567_, 1, v___x_3565_);
    return v___x_3567_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__4,
    );
    v___x_3569_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3570_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1;
    v___x_3571_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3571_, 0, v___x_3570_);
    crate::leanh::lean_closure_set(v___x_3571_, 1, v___x_3569_);
    crate::leanh::lean_closure_set(v___x_3571_, 2, v___x_3568_);
    return v___x_3571_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter(
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3577_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__0;
    v___x_3578_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___closed__5,
    );
    v___x_3579_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3577_,
        v___x_3578_,
        v_a_3572_,
        v_a_3573_,
        v_a_3574_,
        v_a_3575_,
    );
    return v___x_3579_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed(
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
    mut v_a_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3585_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter(
        v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_,
    );
    crate::leanh::lean_dec(v_a_3583_);
    crate::leanh::lean_dec_ref(v_a_3582_);
    crate::leanh::lean_dec(v_a_3581_);
    crate::leanh::lean_dec_ref(v_a_3580_);
    return v_res_3585_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3594_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3595_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1;
    v___x_3596_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___closed__0;
    v___x_3597_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3598_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3594_,
        v___x_3595_,
        v___x_3596_,
        v___x_3597_,
    );
    return v___x_3598_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51___boxed(
    mut v_a_3599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51();
    return v_res_3600_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3615_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_formatter___closed__4,
    );
    v___x_3616_ = l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__3;
    v___x_3617_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3617_, 0, v___x_3616_);
    crate::leanh::lean_closure_set(v___x_3617_, 1, v___x_3615_);
    return v___x_3617_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3618_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__4,
    );
    v___x_3619_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3620_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__1;
    v___x_3621_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3621_, 0, v___x_3620_);
    crate::leanh::lean_closure_set(v___x_3621_, 1, v___x_3619_);
    crate::leanh::lean_closure_set(v___x_3621_, 2, v___x_3618_);
    return v___x_3621_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_defEq_formatter(
    mut v_a_3622_: *mut crate::leanh::LeanObject,
    mut v_a_3623_: *mut crate::leanh::LeanObject,
    mut v_a_3624_: *mut crate::leanh::LeanObject,
    mut v_a_3625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3627_ = l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__0;
    v___x_3628_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5_once),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq_formatter___closed__5,
    );
    v___x_3629_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3627_,
        v___x_3628_,
        v_a_3622_,
        v_a_3623_,
        v_a_3624_,
        v_a_3625_,
    );
    return v___x_3629_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed(
    mut v_a_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_a_3633_: *mut crate::leanh::LeanObject,
    mut v_a_3634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3635_ = l_Lean_Parser_Command_GrindCnstr_defEq_formatter(
        v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_,
    );
    crate::leanh::lean_dec(v_a_3633_);
    crate::leanh::lean_dec_ref(v_a_3632_);
    crate::leanh::lean_dec(v_a_3631_);
    crate::leanh::lean_dec_ref(v_a_3630_);
    return v_res_3635_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3644_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3645_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__1;
    v___x_3646_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___closed__0;
    v___x_3647_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3648_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3644_,
        v___x_3645_,
        v___x_3646_,
        v___x_3647_,
    );
    return v___x_3648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55___boxed(
    mut v_a_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55();
    return v_res_3650_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3651_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_defEq_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3652_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notDefEq_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3653_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3653_, 0, v___x_3652_);
    crate::leanh::lean_closure_set(v___x_3653_, 1, v___x_3651_);
    return v___x_3653_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__0,
    );
    v___x_3655_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_check_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3656_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3656_, 0, v___x_3655_);
    crate::leanh::lean_closure_set(v___x_3656_, 1, v___x_3654_);
    return v___x_3656_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__1,
    );
    v___x_3658_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_guard_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3659_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3659_, 0, v___x_3658_);
    crate::leanh::lean_closure_set(v___x_3659_, 1, v___x_3657_);
    return v___x_3659_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3660_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__2,
    );
    v___x_3661_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_maxInsts_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3662_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3662_, 0, v___x_3661_);
    crate::leanh::lean_closure_set(v___x_3662_, 1, v___x_3660_);
    return v___x_3662_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3663_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__3,
    );
    v___x_3664_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_genLt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3665_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3665_, 0, v___x_3664_);
    crate::leanh::lean_closure_set(v___x_3665_, 1, v___x_3663_);
    return v___x_3665_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3666_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__4,
    );
    v___x_3667_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_depthLt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3668_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3668_, 0, v___x_3667_);
    crate::leanh::lean_closure_set(v___x_3668_, 1, v___x_3666_);
    return v___x_3668_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3669_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__5,
    );
    v___x_3670_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_sizeLt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3671_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3671_, 0, v___x_3670_);
    crate::leanh::lean_closure_set(v___x_3671_, 1, v___x_3669_);
    return v___x_3671_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__6,
    );
    v___x_3673_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isGround_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3674_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3674_, 0, v___x_3673_);
    crate::leanh::lean_closure_set(v___x_3674_, 1, v___x_3672_);
    return v___x_3674_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3675_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__7,
    );
    v___x_3676_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3677_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3677_, 0, v___x_3676_);
    crate::leanh::lean_closure_set(v___x_3677_, 1, v___x_3675_);
    return v___x_3677_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3678_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__8,
    );
    v___x_3679_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notValue_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3680_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3680_, 0, v___x_3679_);
    crate::leanh::lean_closure_set(v___x_3680_, 1, v___x_3678_);
    return v___x_3680_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3681_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9_once),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__9,
    );
    v___x_3682_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3683_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3683_, 0, v___x_3682_);
    crate::leanh::lean_closure_set(v___x_3683_, 1, v___x_3681_);
    return v___x_3683_;
}
pub unsafe fn l_Lean_Parser_Command_grindPatternCnstr_formatter(
    mut v_a_3684_: *mut crate::leanh::LeanObject,
    mut v_a_3685_: *mut crate::leanh::LeanObject,
    mut v_a_3686_: *mut crate::leanh::LeanObject,
    mut v_a_3687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3689_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isValue_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3690_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_formatter___closed__10,
    );
    v___x_3691_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3689_,
        v___x_3690_,
        v_a_3684_,
        v_a_3685_,
        v_a_3686_,
        v_a_3687_,
    );
    return v___x_3691_;
}
pub unsafe fn l_Lean_Parser_Command_grindPatternCnstr_formatter___boxed(
    mut v_a_3692_: *mut crate::leanh::LeanObject,
    mut v_a_3693_: *mut crate::leanh::LeanObject,
    mut v_a_3694_: *mut crate::leanh::LeanObject,
    mut v_a_3695_: *mut crate::leanh::LeanObject,
    mut v_a_3696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3697_ = l_Lean_Parser_Command_grindPatternCnstr_formatter(
        v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_,
    );
    crate::leanh::lean_dec(v_a_3695_);
    crate::leanh::lean_dec_ref(v_a_3694_);
    crate::leanh::lean_dec(v_a_3693_);
    crate::leanh::lean_dec_ref(v_a_3692_);
    return v_res_3697_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3707_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_grindPatternCnstr_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3708_ = crate::leanh::lean_alloc_closure(
        l_Lean_ppLine_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3709_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3709_, 0, v___x_3708_);
    crate::leanh::lean_closure_set(v___x_3709_, 1, v___x_3707_);
    return v___x_3709_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__2,
    );
    v___x_3711_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_many1Indent_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3711_, 0, v___x_3710_);
    return v___x_3711_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__3,
    );
    v___x_3713_ = l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__1;
    v___x_3714_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3714_, 0, v___x_3713_);
    crate::leanh::lean_closure_set(v___x_3714_, 1, v___x_3712_);
    return v___x_3714_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3715_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__4,
    );
    v___x_3716_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3717_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__1;
    v___x_3718_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3718_, 0, v___x_3717_);
    crate::leanh::lean_closure_set(v___x_3718_, 1, v___x_3716_);
    crate::leanh::lean_closure_set(v___x_3718_, 2, v___x_3715_);
    return v___x_3718_;
}
pub unsafe fn l_Lean_Parser_Command_grindPatternCnstrs_formatter(
    mut v_a_3719_: *mut crate::leanh::LeanObject,
    mut v_a_3720_: *mut crate::leanh::LeanObject,
    mut v_a_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__0;
    v___x_3725_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstrs_formatter___closed__5,
    );
    v___x_3726_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3724_,
        v___x_3725_,
        v_a_3719_,
        v_a_3720_,
        v_a_3721_,
        v_a_3722_,
    );
    return v___x_3726_;
}
pub unsafe fn l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed(
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3732_ = l_Lean_Parser_Command_grindPatternCnstrs_formatter(
        v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_,
    );
    crate::leanh::lean_dec(v_a_3730_);
    crate::leanh::lean_dec_ref(v_a_3729_);
    crate::leanh::lean_dec(v_a_3728_);
    crate::leanh::lean_dec_ref(v_a_3727_);
    return v_res_3732_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3740_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3741_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__1;
    v___x_3742_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___closed__0;
    v___x_3743_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3744_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3740_,
        v___x_3741_,
        v___x_3742_,
        v___x_3743_,
    );
    return v___x_3744_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61___boxed(
    mut v_a_3745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3746_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61();
    return v_res_3746_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_formatter___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3778_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_grindPatternCnstrs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3779_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3779_, 0, v___x_3778_);
    return v___x_3779_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_formatter___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__11_once),
        _init_l_Lean_Parser_Command_grindPattern_formatter___closed__11,
    );
    v___x_3781_ = l_Lean_Parser_Command_grindPattern_formatter___closed__10;
    v___x_3782_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3782_, 0, v___x_3781_);
    crate::leanh::lean_closure_set(v___x_3782_, 1, v___x_3780_);
    return v___x_3782_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_formatter___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3783_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__12_once),
        _init_l_Lean_Parser_Command_grindPattern_formatter___closed__12,
    );
    v___x_3784_ = l_Lean_Parser_Command_grindPattern_formatter___closed__8;
    v___x_3785_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3785_, 0, v___x_3784_);
    crate::leanh::lean_closure_set(v___x_3785_, 1, v___x_3783_);
    return v___x_3785_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_formatter___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3786_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__13_once),
        _init_l_Lean_Parser_Command_grindPattern_formatter___closed__13,
    );
    v___x_3787_ = l_Lean_Parser_Command_GrindCnstr_isValue_formatter___closed__2;
    v___x_3788_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3788_, 0, v___x_3787_);
    crate::leanh::lean_closure_set(v___x_3788_, 1, v___x_3786_);
    return v___x_3788_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_formatter___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3789_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__14_once),
        _init_l_Lean_Parser_Command_grindPattern_formatter___closed__14,
    );
    v___x_3790_ = l_Lean_Parser_Command_grindPattern_formatter___closed__7;
    v___x_3791_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3791_, 0, v___x_3790_);
    crate::leanh::lean_closure_set(v___x_3791_, 1, v___x_3789_);
    return v___x_3791_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_formatter___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3792_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__15_once),
        _init_l_Lean_Parser_Command_grindPattern_formatter___closed__15,
    );
    v___x_3793_ = l_Lean_Parser_Command_grindPattern_formatter___closed__2;
    v___x_3794_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3794_, 0, v___x_3793_);
    crate::leanh::lean_closure_set(v___x_3794_, 1, v___x_3792_);
    return v___x_3794_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_formatter___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3795_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__16_once),
        _init_l_Lean_Parser_Command_grindPattern_formatter___closed__16,
    );
    v___x_3796_ = l_Lean_Parser_Command_grindPattern_formatter___closed__1;
    v___x_3797_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3797_, 0, v___x_3796_);
    crate::leanh::lean_closure_set(v___x_3797_, 1, v___x_3795_);
    return v___x_3797_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_formatter___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__17_once),
        _init_l_Lean_Parser_Command_grindPattern_formatter___closed__17,
    );
    v___x_3799_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3800_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_3801_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3801_, 0, v___x_3800_);
    crate::leanh::lean_closure_set(v___x_3801_, 1, v___x_3799_);
    crate::leanh::lean_closure_set(v___x_3801_, 2, v___x_3798_);
    return v___x_3801_;
}
pub unsafe fn l_Lean_Parser_Command_grindPattern_formatter(
    mut v_a_3802_: *mut crate::leanh::LeanObject,
    mut v_a_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
    mut v_a_3805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3807_ = l_Lean_Parser_Command_grindPattern_formatter___closed__0;
    v___x_3808_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_formatter___closed__18_once),
        _init_l_Lean_Parser_Command_grindPattern_formatter___closed__18,
    );
    v___x_3809_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3807_,
        v___x_3808_,
        v_a_3802_,
        v_a_3803_,
        v_a_3804_,
        v_a_3805_,
    );
    return v___x_3809_;
}
pub unsafe fn l_Lean_Parser_Command_grindPattern_formatter___boxed(
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_a_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3815_ =
        l_Lean_Parser_Command_grindPattern_formatter(v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
    crate::leanh::lean_dec(v_a_3813_);
    crate::leanh::lean_dec_ref(v_a_3812_);
    crate::leanh::lean_dec(v_a_3811_);
    crate::leanh::lean_dec_ref(v_a_3810_);
    return v_res_3815_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3824_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_3825_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___closed__0;
    v___x_3826_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_grindPattern_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3827_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3823_,
        v___x_3824_,
        v___x_3825_,
        v___x_3826_,
    );
    return v___x_3827_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65___boxed(
    mut v_a_3828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3829_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65();
    return v_res_3829_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer(
    mut v_a_3856_: *mut crate::leanh::LeanObject,
    mut v_a_3857_: *mut crate::leanh::LeanObject,
    mut v_a_3858_: *mut crate::leanh::LeanObject,
    mut v_a_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3861_ = l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__0;
    v___x_3862_ = l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__7;
    v___x_3863_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3861_,
        v___x_3862_,
        v_a_3856_,
        v_a_3857_,
        v_a_3858_,
        v_a_3859_,
    );
    return v___x_3863_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed(
    mut v_a_3864_: *mut crate::leanh::LeanObject,
    mut v_a_3865_: *mut crate::leanh::LeanObject,
    mut v_a_3866_: *mut crate::leanh::LeanObject,
    mut v_a_3867_: *mut crate::leanh::LeanObject,
    mut v_a_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer(
        v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_,
    );
    crate::leanh::lean_dec(v_a_3867_);
    crate::leanh::lean_dec_ref(v_a_3866_);
    crate::leanh::lean_dec(v_a_3865_);
    crate::leanh::lean_dec_ref(v_a_3864_);
    return v_res_3869_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3879_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3880_ = l_Lean_Parser_Command_GrindCnstr_isValue___closed__5;
    v___x_3881_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___closed__1;
    v___x_3882_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3883_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3879_,
        v___x_3880_,
        v___x_3881_,
        v___x_3882_,
    );
    return v___x_3883_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69___boxed(
    mut v_a_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3885_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69();
    return v_res_3885_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer(
    mut v_a_3904_: *mut crate::leanh::LeanObject,
    mut v_a_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v_a_3907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3909_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__0;
    v___x_3910_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___closed__3;
    v___x_3911_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3909_,
        v___x_3910_,
        v_a_3904_,
        v_a_3905_,
        v_a_3906_,
        v_a_3907_,
    );
    return v___x_3911_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed(
    mut v_a_3912_: *mut crate::leanh::LeanObject,
    mut v_a_3913_: *mut crate::leanh::LeanObject,
    mut v_a_3914_: *mut crate::leanh::LeanObject,
    mut v_a_3915_: *mut crate::leanh::LeanObject,
    mut v_a_3916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3917_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer(
        v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_,
    );
    crate::leanh::lean_dec(v_a_3915_);
    crate::leanh::lean_dec_ref(v_a_3914_);
    crate::leanh::lean_dec(v_a_3913_);
    crate::leanh::lean_dec_ref(v_a_3912_);
    return v_res_3917_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3926_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3927_ = l_Lean_Parser_Command_GrindCnstr_isStrictValue___closed__1;
    v___x_3928_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___closed__0;
    v___x_3929_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3930_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3926_,
        v___x_3927_,
        v___x_3928_,
        v___x_3929_,
    );
    return v___x_3930_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73___boxed(
    mut v_a_3931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3932_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73();
    return v_res_3932_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer(
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_a_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3956_ = l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__0;
    v___x_3957_ = l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___closed__3;
    v___x_3958_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3956_,
        v___x_3957_,
        v_a_3951_,
        v_a_3952_,
        v_a_3953_,
        v_a_3954_,
    );
    return v___x_3958_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed(
    mut v_a_3959_: *mut crate::leanh::LeanObject,
    mut v_a_3960_: *mut crate::leanh::LeanObject,
    mut v_a_3961_: *mut crate::leanh::LeanObject,
    mut v_a_3962_: *mut crate::leanh::LeanObject,
    mut v_a_3963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ = l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer(
        v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_,
    );
    crate::leanh::lean_dec(v_a_3962_);
    crate::leanh::lean_dec_ref(v_a_3961_);
    crate::leanh::lean_dec(v_a_3960_);
    crate::leanh::lean_dec_ref(v_a_3959_);
    return v_res_3964_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3973_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3974_ = l_Lean_Parser_Command_GrindCnstr_notValue___closed__1;
    v___x_3975_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___closed__0;
    v___x_3976_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3977_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3973_,
        v___x_3974_,
        v___x_3975_,
        v___x_3976_,
    );
    return v___x_3977_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77___boxed(
    mut v_a_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77();
    return v_res_3979_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer(
    mut v_a_3998_: *mut crate::leanh::LeanObject,
    mut v_a_3999_: *mut crate::leanh::LeanObject,
    mut v_a_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4003_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__0;
    v___x_4004_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___closed__3;
    v___x_4005_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4003_,
        v___x_4004_,
        v_a_3998_,
        v_a_3999_,
        v_a_4000_,
        v_a_4001_,
    );
    return v___x_4005_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed(
    mut v_a_4006_: *mut crate::leanh::LeanObject,
    mut v_a_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
    mut v_a_4010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4011_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer(
        v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_,
    );
    crate::leanh::lean_dec(v_a_4009_);
    crate::leanh::lean_dec_ref(v_a_4008_);
    crate::leanh::lean_dec(v_a_4007_);
    crate::leanh::lean_dec_ref(v_a_4006_);
    return v_res_4011_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4020_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4021_ = l_Lean_Parser_Command_GrindCnstr_notStrictValue___closed__1;
    v___x_4022_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___closed__0;
    v___x_4023_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4024_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4020_,
        v___x_4021_,
        v___x_4022_,
        v___x_4023_,
    );
    return v___x_4024_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81___boxed(
    mut v_a_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4026_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81();
    return v_res_4026_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer(
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
    mut v_a_4047_: *mut crate::leanh::LeanObject,
    mut v_a_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__0;
    v___x_4051_ = l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___closed__3;
    v___x_4052_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4050_,
        v___x_4051_,
        v_a_4045_,
        v_a_4046_,
        v_a_4047_,
        v_a_4048_,
    );
    return v___x_4052_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed(
    mut v_a_4053_: *mut crate::leanh::LeanObject,
    mut v_a_4054_: *mut crate::leanh::LeanObject,
    mut v_a_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4058_ = l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer(
        v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_,
    );
    crate::leanh::lean_dec(v_a_4056_);
    crate::leanh::lean_dec_ref(v_a_4055_);
    crate::leanh::lean_dec(v_a_4054_);
    crate::leanh::lean_dec_ref(v_a_4053_);
    return v_res_4058_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4067_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4068_ = l_Lean_Parser_Command_GrindCnstr_isGround___closed__1;
    v___x_4069_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___closed__0;
    v___x_4070_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4071_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4067_,
        v___x_4068_,
        v___x_4069_,
        v___x_4070_,
    );
    return v___x_4071_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85___boxed(
    mut v_a_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4073_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85();
    return v_res_4073_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer(
    mut v_a_4104_: *mut crate::leanh::LeanObject,
    mut v_a_4105_: *mut crate::leanh::LeanObject,
    mut v_a_4106_: *mut crate::leanh::LeanObject,
    mut v_a_4107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4109_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__0;
    v___x_4110_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___closed__8;
    v___x_4111_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4109_,
        v___x_4110_,
        v_a_4104_,
        v_a_4105_,
        v_a_4106_,
        v_a_4107_,
    );
    return v___x_4111_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed(
    mut v_a_4112_: *mut crate::leanh::LeanObject,
    mut v_a_4113_: *mut crate::leanh::LeanObject,
    mut v_a_4114_: *mut crate::leanh::LeanObject,
    mut v_a_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4117_ = l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer(
        v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_,
    );
    crate::leanh::lean_dec(v_a_4115_);
    crate::leanh::lean_dec_ref(v_a_4114_);
    crate::leanh::lean_dec(v_a_4113_);
    crate::leanh::lean_dec_ref(v_a_4112_);
    return v_res_4117_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4126_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4127_ = l_Lean_Parser_Command_GrindCnstr_sizeLt___closed__1;
    v___x_4128_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___closed__0;
    v___x_4129_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4130_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4126_,
        v___x_4127_,
        v___x_4128_,
        v___x_4129_,
    );
    return v___x_4130_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89___boxed(
    mut v_a_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4132_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89();
    return v_res_4132_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer(
    mut v_a_4151_: *mut crate::leanh::LeanObject,
    mut v_a_4152_: *mut crate::leanh::LeanObject,
    mut v_a_4153_: *mut crate::leanh::LeanObject,
    mut v_a_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__0;
    v___x_4157_ = l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___closed__3;
    v___x_4158_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4156_,
        v___x_4157_,
        v_a_4151_,
        v_a_4152_,
        v_a_4153_,
        v_a_4154_,
    );
    return v___x_4158_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed(
    mut v_a_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
    mut v_a_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4164_ = l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer(
        v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_,
    );
    crate::leanh::lean_dec(v_a_4162_);
    crate::leanh::lean_dec_ref(v_a_4161_);
    crate::leanh::lean_dec(v_a_4160_);
    crate::leanh::lean_dec_ref(v_a_4159_);
    return v_res_4164_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4173_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4174_ = l_Lean_Parser_Command_GrindCnstr_depthLt___closed__1;
    v___x_4175_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___closed__0;
    v___x_4176_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4177_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4173_,
        v___x_4174_,
        v___x_4175_,
        v___x_4176_,
    );
    return v___x_4177_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93___boxed(
    mut v_a_4178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4179_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93();
    return v_res_4179_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer(
    mut v_a_4198_: *mut crate::leanh::LeanObject,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4203_ = l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__0;
    v___x_4204_ = l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___closed__3;
    v___x_4205_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4203_,
        v___x_4204_,
        v_a_4198_,
        v_a_4199_,
        v_a_4200_,
        v_a_4201_,
    );
    return v___x_4205_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed(
    mut v_a_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer(
        v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_,
    );
    crate::leanh::lean_dec(v_a_4209_);
    crate::leanh::lean_dec_ref(v_a_4208_);
    crate::leanh::lean_dec(v_a_4207_);
    crate::leanh::lean_dec_ref(v_a_4206_);
    return v_res_4211_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4220_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4221_ = l_Lean_Parser_Command_GrindCnstr_genLt___closed__1;
    v___x_4222_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___closed__0;
    v___x_4223_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4224_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4220_,
        v___x_4221_,
        v___x_4222_,
        v___x_4223_,
    );
    return v___x_4224_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97___boxed(
    mut v_a_4225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4226_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97();
    return v_res_4226_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer(
    mut v_a_4245_: *mut crate::leanh::LeanObject,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__0;
    v___x_4251_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___closed__3;
    v___x_4252_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4250_,
        v___x_4251_,
        v_a_4245_,
        v_a_4246_,
        v_a_4247_,
        v_a_4248_,
    );
    return v___x_4252_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed(
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
    mut v_a_4257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4258_ = l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer(
        v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_,
    );
    crate::leanh::lean_dec(v_a_4256_);
    crate::leanh::lean_dec_ref(v_a_4255_);
    crate::leanh::lean_dec(v_a_4254_);
    crate::leanh::lean_dec_ref(v_a_4253_);
    return v_res_4258_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4267_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4268_ = l_Lean_Parser_Command_GrindCnstr_maxInsts___closed__1;
    v___x_4269_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___closed__0;
    v___x_4270_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4271_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4267_,
        v___x_4268_,
        v___x_4269_,
        v___x_4270_,
    );
    return v___x_4271_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101___boxed(
    mut v_a_4272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4273_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101();
    return v_res_4273_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4290_ = l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__3;
    v___x_4291_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4292_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4292_, 0, v___x_4291_);
    crate::leanh::lean_closure_set(v___x_4292_, 1, v___x_4290_);
    return v___x_4292_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4,
    );
    v___x_4294_ = l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__1;
    v___x_4295_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4295_, 0, v___x_4294_);
    crate::leanh::lean_closure_set(v___x_4295_, 1, v___x_4293_);
    return v___x_4295_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4296_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__5,
    );
    v___x_4297_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4298_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__1;
    v___x_4299_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4299_, 0, v___x_4298_);
    crate::leanh::lean_closure_set(v___x_4299_, 1, v___x_4297_);
    crate::leanh::lean_closure_set(v___x_4299_, 2, v___x_4296_);
    return v___x_4299_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer(
    mut v_a_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
    mut v_a_4303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4305_ = l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__0;
    v___x_4306_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__6,
    );
    v___x_4307_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4305_,
        v___x_4306_,
        v_a_4300_,
        v_a_4301_,
        v_a_4302_,
        v_a_4303_,
    );
    return v___x_4307_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed(
    mut v_a_4308_: *mut crate::leanh::LeanObject,
    mut v_a_4309_: *mut crate::leanh::LeanObject,
    mut v_a_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4313_ = l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer(
        v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_,
    );
    crate::leanh::lean_dec(v_a_4311_);
    crate::leanh::lean_dec_ref(v_a_4310_);
    crate::leanh::lean_dec(v_a_4309_);
    crate::leanh::lean_dec_ref(v_a_4308_);
    return v_res_4313_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4322_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4323_ = l_Lean_Parser_Command_GrindCnstr_guard___closed__1;
    v___x_4324_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___closed__0;
    v___x_4325_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4326_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4322_,
        v___x_4323_,
        v___x_4324_,
        v___x_4325_,
    );
    return v___x_4326_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105___boxed(
    mut v_a_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4328_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105();
    return v_res_4328_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4340_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4,
    );
    v___x_4341_ = l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__1;
    v___x_4342_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4342_, 0, v___x_4341_);
    crate::leanh::lean_closure_set(v___x_4342_, 1, v___x_4340_);
    return v___x_4342_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4343_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__2,
    );
    v___x_4344_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4345_ = l_Lean_Parser_Command_GrindCnstr_check___closed__1;
    v___x_4346_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4346_, 0, v___x_4345_);
    crate::leanh::lean_closure_set(v___x_4346_, 1, v___x_4344_);
    crate::leanh::lean_closure_set(v___x_4346_, 2, v___x_4343_);
    return v___x_4346_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_check_parenthesizer(
    mut v_a_4347_: *mut crate::leanh::LeanObject,
    mut v_a_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4352_ = l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__0;
    v___x_4353_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___closed__3,
    );
    v___x_4354_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4352_,
        v___x_4353_,
        v_a_4347_,
        v_a_4348_,
        v_a_4349_,
        v_a_4350_,
    );
    return v___x_4354_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed(
    mut v_a_4355_: *mut crate::leanh::LeanObject,
    mut v_a_4356_: *mut crate::leanh::LeanObject,
    mut v_a_4357_: *mut crate::leanh::LeanObject,
    mut v_a_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4360_ = l_Lean_Parser_Command_GrindCnstr_check_parenthesizer(
        v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_,
    );
    crate::leanh::lean_dec(v_a_4358_);
    crate::leanh::lean_dec_ref(v_a_4357_);
    crate::leanh::lean_dec(v_a_4356_);
    crate::leanh::lean_dec_ref(v_a_4355_);
    return v_res_4360_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4369_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4370_ = l_Lean_Parser_Command_GrindCnstr_check___closed__1;
    v___x_4371_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___closed__0;
    v___x_4372_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4373_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4369_,
        v___x_4370_,
        v___x_4371_,
        v___x_4372_,
    );
    return v___x_4373_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109___boxed(
    mut v_a_4374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109();
    return v_res_4375_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0(
    mut v___x_4376_: *mut crate::leanh::LeanObject,
    mut v___x_4377_: *mut crate::leanh::LeanObject,
    mut v___y_4378_: *mut crate::leanh::LeanObject,
    mut v___y_4379_: *mut crate::leanh::LeanObject,
    mut v___y_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4383_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(
        v___x_4376_,
        v___x_4377_,
        v___y_4378_,
        v___y_4379_,
        v___y_4380_,
        v___y_4381_,
    );
    return v___x_4383_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0___boxed(
    mut v___x_4384_: *mut crate::leanh::LeanObject,
    mut v___x_4385_: *mut crate::leanh::LeanObject,
    mut v___y_4386_: *mut crate::leanh::LeanObject,
    mut v___y_4387_: *mut crate::leanh::LeanObject,
    mut v___y_4388_: *mut crate::leanh::LeanObject,
    mut v___y_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4391_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___lam__0(
        v___x_4384_,
        v___x_4385_,
        v___y_4386_,
        v___y_4387_,
        v___y_4388_,
        v___y_4389_,
    );
    crate::leanh::lean_dec(v___y_4389_);
    crate::leanh::lean_dec_ref(v___y_4388_);
    crate::leanh::lean_dec(v___y_4387_);
    crate::leanh::lean_dec_ref(v___y_4386_);
    return v_res_4391_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4404_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4,
    );
    v___f_4405_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__2;
    v___x_4406_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4406_, 0, v___f_4405_);
    crate::leanh::lean_closure_set(v___x_4406_, 1, v___x_4404_);
    return v___x_4406_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4407_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__3,
    );
    v___x_4408_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4409_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1;
    v___x_4410_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4410_, 0, v___x_4409_);
    crate::leanh::lean_closure_set(v___x_4410_, 1, v___x_4408_);
    crate::leanh::lean_closure_set(v___x_4410_, 2, v___x_4407_);
    return v___x_4410_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer(
    mut v_a_4411_: *mut crate::leanh::LeanObject,
    mut v_a_4412_: *mut crate::leanh::LeanObject,
    mut v_a_4413_: *mut crate::leanh::LeanObject,
    mut v_a_4414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4416_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__0;
    v___x_4417_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___closed__4,
    );
    v___x_4418_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4416_,
        v___x_4417_,
        v_a_4411_,
        v_a_4412_,
        v_a_4413_,
        v_a_4414_,
    );
    return v___x_4418_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed(
    mut v_a_4419_: *mut crate::leanh::LeanObject,
    mut v_a_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer(
        v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_,
    );
    crate::leanh::lean_dec(v_a_4422_);
    crate::leanh::lean_dec_ref(v_a_4421_);
    crate::leanh::lean_dec(v_a_4420_);
    crate::leanh::lean_dec_ref(v_a_4419_);
    return v_res_4424_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4433_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4434_ = l_Lean_Parser_Command_GrindCnstr_notDefEq___closed__1;
    v___x_4435_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___closed__0;
    v___x_4436_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4437_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4433_,
        v___x_4434_,
        v___x_4435_,
        v___x_4436_,
    );
    return v___x_4437_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113___boxed(
    mut v_a_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113();
    return v_res_4439_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4452_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___closed__4,
    );
    v___f_4453_ = l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__2;
    v___x_4454_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4454_, 0, v___f_4453_);
    crate::leanh::lean_closure_set(v___x_4454_, 1, v___x_4452_);
    return v___x_4454_;
}
pub unsafe fn _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__3,
    );
    v___x_4456_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4457_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__1;
    v___x_4458_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4458_, 0, v___x_4457_);
    crate::leanh::lean_closure_set(v___x_4458_, 1, v___x_4456_);
    crate::leanh::lean_closure_set(v___x_4458_, 2, v___x_4455_);
    return v___x_4458_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer(
    mut v_a_4459_: *mut crate::leanh::LeanObject,
    mut v_a_4460_: *mut crate::leanh::LeanObject,
    mut v_a_4461_: *mut crate::leanh::LeanObject,
    mut v_a_4462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4464_ = l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__0;
    v___x_4465_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___closed__4,
    );
    v___x_4466_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4464_,
        v___x_4465_,
        v_a_4459_,
        v_a_4460_,
        v_a_4461_,
        v_a_4462_,
    );
    return v___x_4466_;
}
pub unsafe fn l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed(
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4472_ = l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer(
        v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_,
    );
    crate::leanh::lean_dec(v_a_4470_);
    crate::leanh::lean_dec_ref(v_a_4469_);
    crate::leanh::lean_dec(v_a_4468_);
    crate::leanh::lean_dec_ref(v_a_4467_);
    return v_res_4472_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4481_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4482_ = l_Lean_Parser_Command_GrindCnstr_defEq___closed__1;
    v___x_4483_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___closed__0;
    v___x_4484_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4485_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4481_,
        v___x_4482_,
        v___x_4483_,
        v___x_4484_,
    );
    return v___x_4485_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117___boxed(
    mut v_a_4486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4487_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117();
    return v_res_4487_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4488_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4489_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4490_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4490_, 0, v___x_4489_);
    crate::leanh::lean_closure_set(v___x_4490_, 1, v___x_4488_);
    return v___x_4490_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4491_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__0,
    );
    v___x_4492_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_check_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4493_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4493_, 0, v___x_4492_);
    crate::leanh::lean_closure_set(v___x_4493_, 1, v___x_4491_);
    return v___x_4493_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__1,
    );
    v___x_4495_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_guard_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4496_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4496_, 0, v___x_4495_);
    crate::leanh::lean_closure_set(v___x_4496_, 1, v___x_4494_);
    return v___x_4496_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4497_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__2,
    );
    v___x_4498_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4499_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4499_, 0, v___x_4498_);
    crate::leanh::lean_closure_set(v___x_4499_, 1, v___x_4497_);
    return v___x_4499_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4500_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__3,
    );
    v___x_4501_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4502_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4502_, 0, v___x_4501_);
    crate::leanh::lean_closure_set(v___x_4502_, 1, v___x_4500_);
    return v___x_4502_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4503_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__4,
    );
    v___x_4504_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4505_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4505_, 0, v___x_4504_);
    crate::leanh::lean_closure_set(v___x_4505_, 1, v___x_4503_);
    return v___x_4505_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4506_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__5,
    );
    v___x_4507_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4508_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4508_, 0, v___x_4507_);
    crate::leanh::lean_closure_set(v___x_4508_, 1, v___x_4506_);
    return v___x_4508_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4509_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__6,
    );
    v___x_4510_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4511_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4511_, 0, v___x_4510_);
    crate::leanh::lean_closure_set(v___x_4511_, 1, v___x_4509_);
    return v___x_4511_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4512_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__7,
    );
    v___x_4513_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4514_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4514_, 0, v___x_4513_);
    crate::leanh::lean_closure_set(v___x_4514_, 1, v___x_4512_);
    return v___x_4514_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4515_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__8,
    );
    v___x_4516_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4517_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4517_, 0, v___x_4516_);
    crate::leanh::lean_closure_set(v___x_4517_, 1, v___x_4515_);
    return v___x_4517_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4518_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__9,
    );
    v___x_4519_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4520_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4520_, 0, v___x_4519_);
    crate::leanh::lean_closure_set(v___x_4520_, 1, v___x_4518_);
    return v___x_4520_;
}
pub unsafe fn l_Lean_Parser_Command_grindPatternCnstr_parenthesizer(
    mut v_a_4521_: *mut crate::leanh::LeanObject,
    mut v_a_4522_: *mut crate::leanh::LeanObject,
    mut v_a_4523_: *mut crate::leanh::LeanObject,
    mut v_a_4524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4527_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___closed__10,
    );
    v___x_4528_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(
        v___x_4526_,
        v___x_4527_,
        v_a_4521_,
        v_a_4522_,
        v_a_4523_,
        v_a_4524_,
    );
    return v___x_4528_;
}
pub unsafe fn l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___boxed(
    mut v_a_4529_: *mut crate::leanh::LeanObject,
    mut v_a_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_a_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4534_ = l_Lean_Parser_Command_grindPatternCnstr_parenthesizer(
        v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_,
    );
    crate::leanh::lean_dec(v_a_4532_);
    crate::leanh::lean_dec_ref(v_a_4531_);
    crate::leanh::lean_dec(v_a_4530_);
    crate::leanh::lean_dec_ref(v_a_4529_);
    return v_res_4534_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4545_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_grindPatternCnstr_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4546_ = l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__2;
    v___x_4547_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4547_, 0, v___x_4546_);
    crate::leanh::lean_closure_set(v___x_4547_, 1, v___x_4545_);
    return v___x_4547_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4548_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__3,
    );
    v___x_4549_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_many1Indent_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4549_, 0, v___x_4548_);
    return v___x_4549_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4550_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__4,
    );
    v___x_4551_ = l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__1;
    v___x_4552_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4552_, 0, v___x_4551_);
    crate::leanh::lean_closure_set(v___x_4552_, 1, v___x_4550_);
    return v___x_4552_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__5,
    );
    v___x_4554_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4555_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__1;
    v___x_4556_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4556_, 0, v___x_4555_);
    crate::leanh::lean_closure_set(v___x_4556_, 1, v___x_4554_);
    crate::leanh::lean_closure_set(v___x_4556_, 2, v___x_4553_);
    return v___x_4556_;
}
pub unsafe fn l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer(
    mut v_a_4557_: *mut crate::leanh::LeanObject,
    mut v_a_4558_: *mut crate::leanh::LeanObject,
    mut v_a_4559_: *mut crate::leanh::LeanObject,
    mut v_a_4560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4562_ = l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__0;
    v___x_4563_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6_once
        ),
        _init_l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___closed__6,
    );
    v___x_4564_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4562_,
        v___x_4563_,
        v_a_4557_,
        v_a_4558_,
        v_a_4559_,
        v_a_4560_,
    );
    return v___x_4564_;
}
pub unsafe fn l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed(
    mut v_a_4565_: *mut crate::leanh::LeanObject,
    mut v_a_4566_: *mut crate::leanh::LeanObject,
    mut v_a_4567_: *mut crate::leanh::LeanObject,
    mut v_a_4568_: *mut crate::leanh::LeanObject,
    mut v_a_4569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4570_ = l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer(
        v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_,
    );
    crate::leanh::lean_dec(v_a_4568_);
    crate::leanh::lean_dec_ref(v_a_4567_);
    crate::leanh::lean_dec(v_a_4566_);
    crate::leanh::lean_dec_ref(v_a_4565_);
    return v_res_4570_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4578_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4579_ = l_Lean_Parser_Command_grindPatternCnstrs___closed__1;
    v___x_4580_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___closed__0;
    v___x_4581_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4582_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4578_,
        v___x_4579_,
        v___x_4580_,
        v___x_4581_,
    );
    return v___x_4582_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123___boxed(
    mut v_a_4583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4584_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123();
    return v_res_4584_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4616_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_grindPatternCnstrs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4617_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_optional_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4617_, 0, v___x_4616_);
    return v___x_4617_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4618_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11_once),
        _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__11,
    );
    v___x_4619_ = l_Lean_Parser_Command_grindPattern_parenthesizer___closed__10;
    v___x_4620_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4620_, 0, v___x_4619_);
    crate::leanh::lean_closure_set(v___x_4620_, 1, v___x_4618_);
    return v___x_4620_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4621_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12_once),
        _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__12,
    );
    v___x_4622_ = l_Lean_Parser_Command_grindPattern_parenthesizer___closed__8;
    v___x_4623_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4623_, 0, v___x_4622_);
    crate::leanh::lean_closure_set(v___x_4623_, 1, v___x_4621_);
    return v___x_4623_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4624_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13_once),
        _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__13,
    );
    v___x_4625_ = l_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer___closed__2;
    v___x_4626_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4626_, 0, v___x_4625_);
    crate::leanh::lean_closure_set(v___x_4626_, 1, v___x_4624_);
    return v___x_4626_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4627_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14_once),
        _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__14,
    );
    v___x_4628_ = l_Lean_Parser_Command_grindPattern_parenthesizer___closed__7;
    v___x_4629_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4629_, 0, v___x_4628_);
    crate::leanh::lean_closure_set(v___x_4629_, 1, v___x_4627_);
    return v___x_4629_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4630_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15_once),
        _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__15,
    );
    v___x_4631_ = l_Lean_Parser_Command_grindPattern_parenthesizer___closed__2;
    v___x_4632_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4632_, 0, v___x_4631_);
    crate::leanh::lean_closure_set(v___x_4632_, 1, v___x_4630_);
    return v___x_4632_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16_once),
        _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__16,
    );
    v___x_4634_ = l_Lean_Parser_Command_grindPattern_parenthesizer___closed__1;
    v___x_4635_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4635_, 0, v___x_4634_);
    crate::leanh::lean_closure_set(v___x_4635_, 1, v___x_4633_);
    return v___x_4635_;
}
pub unsafe fn _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17_once),
        _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__17,
    );
    v___x_4637_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4638_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_4639_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4639_, 0, v___x_4638_);
    crate::leanh::lean_closure_set(v___x_4639_, 1, v___x_4637_);
    crate::leanh::lean_closure_set(v___x_4639_, 2, v___x_4636_);
    return v___x_4639_;
}
pub unsafe fn l_Lean_Parser_Command_grindPattern_parenthesizer(
    mut v_a_4640_: *mut crate::leanh::LeanObject,
    mut v_a_4641_: *mut crate::leanh::LeanObject,
    mut v_a_4642_: *mut crate::leanh::LeanObject,
    mut v_a_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4645_ = l_Lean_Parser_Command_grindPattern_parenthesizer___closed__0;
    v___x_4646_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18_once),
        _init_l_Lean_Parser_Command_grindPattern_parenthesizer___closed__18,
    );
    v___x_4647_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4645_,
        v___x_4646_,
        v_a_4640_,
        v_a_4641_,
        v_a_4642_,
        v_a_4643_,
    );
    return v___x_4647_;
}
pub unsafe fn l_Lean_Parser_Command_grindPattern_parenthesizer___boxed(
    mut v_a_4648_: *mut crate::leanh::LeanObject,
    mut v_a_4649_: *mut crate::leanh::LeanObject,
    mut v_a_4650_: *mut crate::leanh::LeanObject,
    mut v_a_4651_: *mut crate::leanh::LeanObject,
    mut v_a_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_Parser_Command_grindPattern_parenthesizer(
        v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_,
    );
    crate::leanh::lean_dec(v_a_4651_);
    crate::leanh::lean_dec_ref(v_a_4650_);
    crate::leanh::lean_dec(v_a_4649_);
    crate::leanh::lean_dec_ref(v_a_4648_);
    return v_res_4653_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4662_ = l_Lean_Parser_Command_grindPattern___closed__1;
    v___x_4663_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___closed__0;
    v___x_4664_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_grindPattern_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4665_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4661_,
        v___x_4662_,
        v___x_4663_,
        v___x_4664_,
    );
    return v___x_4665_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127___boxed(
    mut v_a_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4667_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127();
    return v_res_4667_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4674_: u8 = 0;
    let mut v___x_4675_: u8 = 0;
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4674_ = 0;
    v___x_4675_ = 1;
    v___x_4676_ = l_Lean_Parser_Command_initGrindNorm___closed__1;
    v___x_4677_ = l_Lean_Parser_Command_initGrindNorm___closed__0;
    v___x_4678_ = l_Lean_Parser_mkAntiquot(v___x_4677_, v___x_4676_, v___x_4675_, v___x_4674_);
    return v___x_4678_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4680_ = l_Lean_Parser_Command_initGrindNorm___closed__3;
    v___x_4681_ = l_Lean_Parser_symbol(v___x_4680_);
    return v___x_4681_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4682_ = l_Lean_Parser_ident;
    v___x_4683_ = l_Lean_Parser_many(v___x_4682_);
    return v___x_4683_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4685_ = l_Lean_Parser_Command_initGrindNorm___closed__6;
    v___x_4686_ = l_Lean_Parser_symbol(v___x_4685_);
    return v___x_4686_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4687_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__5_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__5,
    );
    v___x_4688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__7_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__7,
    );
    v___x_4689_ = l_Lean_Parser_andthen(v___x_4688_, v___x_4687_);
    return v___x_4689_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4690_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__8_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__8,
    );
    v___x_4691_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__5_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__5,
    );
    v___x_4692_ = l_Lean_Parser_andthen(v___x_4691_, v___x_4690_);
    return v___x_4692_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__9_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__9,
    );
    v___x_4694_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__4_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__4,
    );
    v___x_4695_ = l_Lean_Parser_andthen(v___x_4694_, v___x_4693_);
    return v___x_4695_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4696_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__10_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__10,
    );
    v___x_4697_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4698_ = l_Lean_Parser_Command_initGrindNorm___closed__1;
    v___x_4699_ = l_Lean_Parser_leadingNode(v___x_4698_, v___x_4697_, v___x_4696_);
    return v___x_4699_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4700_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__11_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__11,
    );
    v___x_4701_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__2_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__2,
    );
    v___x_4702_ = l_Lean_Parser_withAntiquot(v___x_4701_, v___x_4700_);
    return v___x_4702_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4703_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__12_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__12,
    );
    v___x_4704_ = l_Lean_Parser_Command_initGrindNorm___closed__1;
    v___x_4705_ = l_Lean_Parser_withCache(v___x_4704_, v___x_4703_);
    return v___x_4705_;
}
pub unsafe fn _init_l_Lean_Parser_Command_initGrindNorm() -> *mut crate::leanh::LeanObject {
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4706_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Command_initGrindNorm___closed__13_once),
        _init_l_Lean_Parser_Command_initGrindNorm___closed__13,
    );
    return v___x_4706_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4708_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1___closed__1;
    v___x_4709_ = l_Lean_Parser_Command_initGrindNorm___closed__1;
    v___x_4710_ = l_Lean_Parser_Command_initGrindNorm;
    v___x_4711_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_4712_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4708_, v___x_4709_, v___x_4710_, v___x_4711_);
    return v___x_4712_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1___boxed(
    mut v_a_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4714_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1();
    return v_res_4714_;
}
pub unsafe fn l_Lean_Parser_Command_initGrindNorm_formatter(
    mut v_a_4741_: *mut crate::leanh::LeanObject,
    mut v_a_4742_: *mut crate::leanh::LeanObject,
    mut v_a_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4746_ = l_Lean_Parser_Command_initGrindNorm_formatter___closed__0;
    v___x_4747_ = l_Lean_Parser_Command_initGrindNorm_formatter___closed__7;
    v___x_4748_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_4746_,
        v___x_4747_,
        v_a_4741_,
        v_a_4742_,
        v_a_4743_,
        v_a_4744_,
    );
    return v___x_4748_;
}
pub unsafe fn l_Lean_Parser_Command_initGrindNorm_formatter___boxed(
    mut v_a_4749_: *mut crate::leanh::LeanObject,
    mut v_a_4750_: *mut crate::leanh::LeanObject,
    mut v_a_4751_: *mut crate::leanh::LeanObject,
    mut v_a_4752_: *mut crate::leanh::LeanObject,
    mut v_a_4753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4754_ =
        l_Lean_Parser_Command_initGrindNorm_formatter(v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
    crate::leanh::lean_dec(v_a_4752_);
    crate::leanh::lean_dec_ref(v_a_4751_);
    crate::leanh::lean_dec(v_a_4750_);
    crate::leanh::lean_dec_ref(v_a_4749_);
    return v_res_4754_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4762_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4763_ = l_Lean_Parser_Command_initGrindNorm___closed__1;
    v___x_4764_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___closed__0;
    v___x_4765_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_initGrindNorm_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4766_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4762_,
        v___x_4763_,
        v___x_4764_,
        v___x_4765_,
    );
    return v___x_4766_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5___boxed(
    mut v_a_4767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4768_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5();
    return v_res_4768_;
}
pub unsafe fn l_Lean_Parser_Command_initGrindNorm_parenthesizer(
    mut v_a_4795_: *mut crate::leanh::LeanObject,
    mut v_a_4796_: *mut crate::leanh::LeanObject,
    mut v_a_4797_: *mut crate::leanh::LeanObject,
    mut v_a_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ = l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__0;
    v___x_4801_ = l_Lean_Parser_Command_initGrindNorm_parenthesizer___closed__7;
    v___x_4802_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4800_,
        v___x_4801_,
        v_a_4795_,
        v_a_4796_,
        v_a_4797_,
        v_a_4798_,
    );
    return v___x_4802_;
}
pub unsafe fn l_Lean_Parser_Command_initGrindNorm_parenthesizer___boxed(
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
    mut v_a_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4808_ = l_Lean_Parser_Command_initGrindNorm_parenthesizer(
        v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_,
    );
    crate::leanh::lean_dec(v_a_4806_);
    crate::leanh::lean_dec_ref(v_a_4805_);
    crate::leanh::lean_dec(v_a_4804_);
    crate::leanh::lean_dec_ref(v_a_4803_);
    return v_res_4808_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4816_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4817_ = l_Lean_Parser_Command_initGrindNorm___closed__1;
    v___x_4818_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___closed__0;
    v___x_4819_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Command_initGrindNorm_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4820_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4816_,
        v___x_4817_,
        v___x_4818_,
        v___x_4819_,
    );
    return v___x_4820_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9___boxed(
    mut v_a_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4822_ = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9();
    return v_res_4822_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Parser(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Command_GrindCnstr_isValue = _init_l_Lean_Parser_Command_GrindCnstr_isValue();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_isValue);
    l_Lean_Parser_Command_GrindCnstr_isStrictValue =
        _init_l_Lean_Parser_Command_GrindCnstr_isStrictValue();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_isStrictValue);
    l_Lean_Parser_Command_GrindCnstr_notValue = _init_l_Lean_Parser_Command_GrindCnstr_notValue();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_notValue);
    l_Lean_Parser_Command_GrindCnstr_notStrictValue =
        _init_l_Lean_Parser_Command_GrindCnstr_notStrictValue();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_notStrictValue);
    l_Lean_Parser_Command_GrindCnstr_isGround = _init_l_Lean_Parser_Command_GrindCnstr_isGround();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_isGround);
    l_Lean_Parser_Command_GrindCnstr_sizeLt = _init_l_Lean_Parser_Command_GrindCnstr_sizeLt();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_sizeLt);
    l_Lean_Parser_Command_GrindCnstr_depthLt = _init_l_Lean_Parser_Command_GrindCnstr_depthLt();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_depthLt);
    l_Lean_Parser_Command_GrindCnstr_genLt = _init_l_Lean_Parser_Command_GrindCnstr_genLt();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_genLt);
    l_Lean_Parser_Command_GrindCnstr_maxInsts = _init_l_Lean_Parser_Command_GrindCnstr_maxInsts();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_maxInsts);
    l_Lean_Parser_Command_GrindCnstr_guard = _init_l_Lean_Parser_Command_GrindCnstr_guard();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_guard);
    l_Lean_Parser_Command_GrindCnstr_check = _init_l_Lean_Parser_Command_GrindCnstr_check();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_check);
    l_Lean_Parser_Command_GrindCnstr_notDefEq = _init_l_Lean_Parser_Command_GrindCnstr_notDefEq();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_notDefEq);
    l_Lean_Parser_Command_GrindCnstr_defEq = _init_l_Lean_Parser_Command_GrindCnstr_defEq();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_GrindCnstr_defEq);
    l_Lean_Parser_Command_grindPatternCnstr = _init_l_Lean_Parser_Command_grindPatternCnstr();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_grindPatternCnstr);
    l_Lean_Parser_Command_grindPatternCnstrs = _init_l_Lean_Parser_Command_grindPatternCnstrs();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_grindPatternCnstrs);
    l_Lean_Parser_Command_grindPattern = _init_l_Lean_Parser_Command_grindPattern();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_grindPattern);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_formatter__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_formatter__15();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_formatter__19();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_formatter__23();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_formatter__27();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_formatter__31();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_formatter__35();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_formatter__39();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_formatter__43();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_formatter__47();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_formatter__51();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_formatter__55();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_formatter__61();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_formatter__65();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isValue_parenthesizer__69();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isStrictValue_parenthesizer__73();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notValue_parenthesizer__77();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notStrictValue_parenthesizer__81();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_isGround_parenthesizer__85();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_sizeLt_parenthesizer__89();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_depthLt_parenthesizer__93();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_genLt_parenthesizer__97();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_maxInsts_parenthesizer__101();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_guard_parenthesizer__105();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_check_parenthesizer__109();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_notDefEq_parenthesizer__113();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_GrindCnstr_defEq_parenthesizer__117();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPatternCnstrs_parenthesizer__123();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_grindPattern___regBuiltin_Lean_Parser_Command_grindPattern_parenthesizer__127();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Command_initGrindNorm = _init_l_Lean_Parser_Command_initGrindNorm();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Command_initGrindNorm);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_formatter__5();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Parser_0__Lean_Parser_Command_initGrindNorm___regBuiltin_Lean_Parser_Command_initGrindNorm_parenthesizer__9();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Parser(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Parser(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
}
