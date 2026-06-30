// Lean compiler output
// Module: Lake.Toml.Grammar
// Imports: Lake.Toml.ParserUtil Lean.Parser Lean.PrettyPrinter.Formatter Lean.PrettyPrinter.Parenthesizer
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_string_append,
    lean_string_push, lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_dec_lt,
};
use crate::r#gen::Init::Prelude::l_Lean_Syntax_isOfKind;
use crate::r#gen::Lake::Toml::ParserUtil::{
    initialize_Lake_Toml_ParserUtil, l_Lake_Toml_chAtom, l_Lake_Toml_chAtom_formatter___boxed,
    l_Lake_Toml_chAtom_parenthesizer___boxed, l_Lake_Toml_chFn, l_Lake_Toml_digitFn,
    l_Lake_Toml_digitPairFn, l_Lake_Toml_dynamicNode, l_Lake_Toml_epsilon_formatter___redArg,
    l_Lake_Toml_epsilon_parenthesizer___redArg, l_Lake_Toml_isBinDigit___boxed,
    l_Lake_Toml_isHexDigit___boxed, l_Lake_Toml_isOctDigit___boxed, l_Lake_Toml_lit,
    l_Lake_Toml_litWithAntiquot, l_Lake_Toml_litWithAntiquot_formatter___redArg,
    l_Lake_Toml_litWithAntiquot_parenthesizer___redArg, l_Lake_Toml_mkUnexpectedCharError,
    l_Lake_Toml_pushLit, l_Lake_Toml_recNodeWithAntiquot,
    l_Lake_Toml_recNodeWithAntiquot_formatter, l_Lake_Toml_recNodeWithAntiquot_parenthesizer,
    l_Lake_Toml_sepByChar1AuxFn, l_Lake_Toml_sepByChar1Fn,
    l_Lake_Toml_sepByLinebreak_formatter___boxed, l_Lake_Toml_sepByLinebreak_parenthesizer___boxed,
    l_Lake_Toml_skipFn___boxed, l_Lake_Toml_strFn, l_Lake_Toml_takeWhile1Fn, l_Lake_Toml_trailing,
    runtime_initialize_Lake_Toml_ParserUtil,
};
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthen, l_Lean_Parser_atomic, l_Lean_Parser_atomicFn,
    l_Lean_Parser_checkLinebreakBefore, l_Lean_Parser_checkStackTop, l_Lean_Parser_hexDigitFn,
    l_Lean_Parser_mkAntiquot, l_Lean_Parser_nodeWithAntiquot, l_Lean_Parser_notFollowedBy,
    l_Lean_Parser_orelse, l_Lean_Parser_pushNone, l_Lean_Parser_sepBy, l_Lean_Parser_sepBy1,
    l_Lean_Parser_sepByNoAntiquot, l_Lean_Parser_setExpected, l_Lean_Parser_symbol,
    l_Lean_Parser_takeUntilFn, l_Lean_Parser_takeWhileFn, l_Lean_Parser_withAntiquot,
    l_Lean_Parser_withAntiquotSpliceAndSuffix,
};
use crate::r#gen::Lean::Parser::Extra::{
    l_Lean_Parser_atomic_formatter___boxed, l_Lean_Parser_mkAntiquot_formatter___boxed,
    l_Lean_Parser_mkAntiquot_parenthesizer___boxed, l_Lean_Parser_nodeWithAntiquot_formatter,
    l_Lean_Parser_nodeWithAntiquot_parenthesizer, l_Lean_Parser_sepBy1_formatter___boxed,
    l_Lean_Parser_sepBy1_parenthesizer___boxed, l_Lean_Parser_setExpected_formatter___boxed,
    l_Lean_Parser_setExpected_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Types::{
    l_Lean_Parser_InputContext_atEnd, l_Lean_Parser_ParserState_mkEOIError,
    l_Lean_Parser_ParserState_mkUnexpectedError, l_Lean_Parser_ParserState_mkUnexpectedErrorAt,
    l_Lean_Parser_ParserState_next_x27___redArg, l_Lean_Parser_ParserState_restore,
    l_Lean_Parser_ParserState_setPos, l_Lean_Parser_ParserState_stackSize,
    l_Lean_Parser_instBEqError_beq, l_Lean_Parser_withCache,
};
use crate::r#gen::Lean::Parser::{initialize_Lean_Parser, runtime_initialize_Lean_Parser};
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    initialize_Lean_PrettyPrinter_Formatter,
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed,
    runtime_initialize_Lean_PrettyPrinter_Formatter,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    initialize_Lean_PrettyPrinter_Parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    runtime_initialize_Lean_PrettyPrinter_Parenthesizer,
};
pub static l_Lake_Toml_wsFn___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_wsFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_wsFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_wsFn___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0_value:
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
        105, 110, 118, 97, 108, 105, 100, 32, 110, 101, 119, 108, 105, 110, 101, 59, 32, 110, 111,
        32, 76, 70, 32, 97, 102, 116, 101, 114, 32, 67, 82, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_newlineFn___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [110, 101, 119, 108, 105, 110, 101, 0],
    };
static mut l_Lake_Toml_newlineFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_newlineFn___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_newlineFn___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_newlineFn___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_newlineFn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_newlineFn___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_isControlChar___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_commentFn___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [99, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lake_Toml_commentFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_commentFn___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_commentFn___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_commentFn___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_commentFn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_commentFn___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        101, 115, 99, 97, 112, 101, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3_value:
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
        115, 116, 114, 105, 110, 103, 32, 103, 97, 112, 32, 105, 115, 32, 102, 111, 114, 98, 105,
        100, 100, 101, 110, 32, 104, 101, 114, 101, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4_value:
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
        105, 110, 118, 97, 108, 105, 100, 32, 101, 115, 99, 97, 112, 101, 32, 115, 101, 113, 117,
        101, 110, 99, 101, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_wsNewlineFn___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        117, 110, 116, 101, 114, 109, 105, 110, 97, 116, 101, 100, 32, 98, 97, 115, 105, 99, 32,
        115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lake_Toml_basicStringFn___closed__0_value: leanh::LeanStringObject<13> =
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
        m_data: [98, 97, 115, 105, 99, 32, 115, 116, 114, 105, 110, 103, 0],
    };
static mut l_Lake_Toml_basicStringFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_basicStringFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_basicStringFn___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_basicStringFn___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_basicStringFn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_basicStringFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        117, 110, 116, 101, 114, 109, 105, 110, 97, 116, 101, 100, 32, 108, 105, 116, 101, 114, 97,
        108, 32, 115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lake_Toml_literalStringFn___closed__0_value: leanh::LeanStringObject<15> =
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
            108, 105, 116, 101, 114, 97, 108, 32, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lake_Toml_literalStringFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_literalStringFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_literalStringFn___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_literalStringFn___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_literalStringFn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_literalStringFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        116, 111, 111, 32, 109, 97, 110, 121, 32, 113, 117, 111, 116, 101, 115, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        117, 110, 116, 101, 114, 109, 105, 110, 97, 116, 101, 100, 32, 109, 117, 108, 116, 105, 45,
        108, 105, 110, 101, 32, 108, 105, 116, 101, 114, 97, 108, 32, 115, 116, 114, 105, 110, 103,
        0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [109, 117, 108, 116, 105, 45, 108, 105, 110, 101, 32, 108, 105, 116, 101, 114, 97, 108, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_mlLiteralStringFn___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_mlLiteralStringFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((3 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_Toml_mlLiteralStringFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlLiteralStringFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        117, 110, 116, 101, 114, 109, 105, 110, 97, 116, 101, 100, 32, 109, 117, 108, 116, 105, 45,
        108, 105, 110, 101, 32, 98, 97, 115, 105, 99, 32, 115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [109, 117, 108, 116, 105, 45, 108, 105, 110, 101, 32, 98, 97, 115, 105, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_mlBasicStringFn___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_mlBasicStringFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((3 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_Toml_mlBasicStringFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlBasicStringFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value:
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
    m_data: [104, 111, 117, 114, 32, 100, 105, 103, 105, 116, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [109, 105, 110, 117, 116, 101, 32, 100, 105, 103, 105, 116, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0_value:
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
        116, 105, 109, 101, 32, 111, 102, 102, 115, 101, 116, 32, 105, 115, 32, 102, 111, 114, 98,
        105, 100, 100, 101, 110, 32, 104, 101, 114, 101, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [109, 105, 108, 108, 105, 115, 101, 99, 111, 110, 100, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [115, 101, 99, 111, 110, 100, 32, 100, 105, 103, 105, 116, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_timeFn___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [104, 111, 117, 114, 0],
    };
static mut l_Lake_Toml_timeFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_timeFn___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_timeFn___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_timeFn___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_timeFn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_timeFn___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [109, 111, 110, 116, 104, 32, 100, 105, 103, 105, 116, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 97, 121, 32, 100, 105, 103, 105, 116, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [121, 101, 97, 114, 32, 100, 105, 103, 105, 116, 0]};
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        100, 101, 99, 105, 109, 97, 108, 32, 101, 120, 112, 111, 110, 101, 110, 116, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value:
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
    m_data: [76, 97, 107, 101, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value:
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
    m_data: [84, 111, 109, 108, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 108, 111, 97, 116, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_0:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut leanh::LeanObject,
        16525079986463702690 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value
        ) as *mut leanh::LeanObject,
        17795691646878718568 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_skipFn___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 101, 99, 73, 110, 116, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_0:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut leanh::LeanObject,
        16525079986463702690 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value
        ) as *mut leanh::LeanObject,
        7221221276125824402 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        100, 101, 99, 105, 109, 97, 108, 32, 102, 114, 97, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        100, 101, 99, 105, 109, 97, 108, 32, 105, 110, 116, 101, 103, 101, 114, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [110, 102, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [39, 105, 110, 102, 39, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [97, 110, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [39, 110, 97, 110, 39, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value:
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
    m_data: [100, 97, 116, 101, 84, 105, 109, 101, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut leanh::LeanObject,
        16525079986463702690 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        14620934732133821028 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 97, 116, 101, 45, 116, 105, 109, 101, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [105, 110, 116, 101, 103, 101, 114, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value
            ) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__2_value: leanh::LeanStringObject<13> =
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
        m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__3_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_isHexDigit___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__4_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
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
            104, 101, 120, 97, 100, 101, 99, 105, 109, 97, 108, 32, 105, 110, 116, 101, 103, 101,
            114, 0,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__4_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__6_value: leanh::LeanStringObject<7> =
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
        m_data: [104, 101, 120, 78, 117, 109, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_numeralFn___lam__0___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__6_value)
                as *mut leanh::LeanObject,
            18206715719635152477 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__8_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_isOctDigit___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__9_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            111, 99, 116, 97, 108, 32, 105, 110, 116, 101, 103, 101, 114, 0,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__9_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__11_value: leanh::LeanStringObject<7> =
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
        m_data: [111, 99, 116, 78, 117, 109, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_numeralFn___lam__0___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__11_value)
                as *mut leanh::LeanObject,
            14236009889605174877 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__13_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_isBinDigit___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__14_value: leanh::LeanStringObject<15> =
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
            98, 105, 110, 97, 114, 121, 32, 105, 110, 116, 101, 103, 101, 114, 0,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__14_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__16_value: leanh::LeanStringObject<7> =
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
        m_data: [98, 105, 110, 78, 117, 109, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__16_value)
        as *mut leanh::LeanObject;
static l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_numeralFn___lam__0___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__16_value)
                as *mut leanh::LeanObject,
            486821199203679291 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_numeralFn___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_numeralFn___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_numeralFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_trailingWs___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_trailingWs___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_trailingWs: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_trailingSep___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_trailingFn___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_trailingSep___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_trailingSep___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_trailingSep___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_trailingSep___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_trailingSep: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_unquotedKeyFn___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_unquotedKeyFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_unquotedKeyFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKeyFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_unquotedKeyFn___closed__1_value: leanh::LeanStringObject<13> =
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
        m_data: [117, 110, 113, 117, 111, 116, 101, 100, 32, 107, 101, 121, 0],
    };
static mut l_Lake_Toml_unquotedKeyFn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKeyFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_unquotedKeyFn___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_unquotedKeyFn___closed__1_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_unquotedKeyFn___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKeyFn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Toml_unquotedKey___closed__0_value: leanh::LeanStringObject<12> =
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
        m_data: [117, 110, 113, 117, 111, 116, 101, 100, 75, 101, 121, 0],
    };
static mut l_Lake_Toml_unquotedKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_unquotedKey___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_unquotedKey___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_unquotedKey___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__0_value)
                as *mut leanh::LeanObject,
            17377064587868252984 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_unquotedKey___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_unquotedKey___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_unquotedKey___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_unquotedKey: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_basicString___closed__0_value: leanh::LeanStringObject<12> =
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
        m_data: [98, 97, 115, 105, 99, 83, 116, 114, 105, 110, 103, 0],
    };
static mut l_Lake_Toml_basicString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_basicString___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_basicString___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_basicString___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_basicString___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_basicString___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_basicString___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_basicString___closed__0_value)
                as *mut leanh::LeanObject,
            16849499249217381028 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_basicString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_basicString___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_basicString___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_basicString___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_basicString: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_literalString___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            108, 105, 116, 101, 114, 97, 108, 83, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lake_Toml_literalString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_literalString___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Toml_literalString___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_literalString___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_literalString___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_literalString___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_literalString___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_literalString___closed__0_value)
                as *mut leanh::LeanObject,
            6024408818386315505 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_literalString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_literalString___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Toml_literalString___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_literalString___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_literalString: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_mlBasicString___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            109, 108, 66, 97, 115, 105, 99, 83, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lake_Toml_mlBasicString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Toml_mlBasicString___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_mlBasicString___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_mlBasicString___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__0_value)
                as *mut leanh::LeanObject,
            1863697331681762253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_mlBasicString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Toml_mlBasicString___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_mlBasicString___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_mlBasicString: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_mlLiteralString___closed__0_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            109, 108, 76, 105, 116, 101, 114, 97, 108, 83, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lake_Toml_mlLiteralString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_Toml_mlLiteralString___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_mlLiteralString___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_mlLiteralString___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__0_value)
                as *mut leanh::LeanObject,
            3891709539368753145 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_mlLiteralString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Toml_mlLiteralString___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_mlLiteralString___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_mlLiteralString: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_quotedKey___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_quotedKey___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_quotedKey: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_simpleKey___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 105, 109, 112, 108, 101, 75, 101, 121, 0],
    };
static mut l_Lake_Toml_simpleKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_simpleKey___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_simpleKey___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_simpleKey___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__0_value)
                as *mut leanh::LeanObject,
            15900767148364346299 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_simpleKey___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_simpleKey___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_simpleKey___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_simpleKey___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_simpleKey___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_simpleKey: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_key___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [107, 101, 121, 0],
    };
static mut l_Lake_Toml_key___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_key___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_key___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_key___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_key___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_key___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_key___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_key___closed__0_value) as *mut leanh::LeanObject,
            3865642880800790572 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_key___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_key___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_key___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_key___closed__0_value) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_key___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_key___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_key___closed__3_value: leanh::LeanStringObject<2> =
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
        m_data: [46, 0],
    };
static mut l_Lake_Toml_key___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_key___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_key___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_key: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_stdTable___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [115, 116, 100, 84, 97, 98, 108, 101, 0],
    };
static mut l_Lake_Toml_stdTable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_stdTable___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_stdTable___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_stdTable___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__0_value)
                as *mut leanh::LeanObject,
            14174431292734320076 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_stdTable___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_stdTable___closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 97, 98, 108, 101, 0],
    };
static mut l_Lake_Toml_stdTable___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_stdTable___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__2_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_stdTable___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_stdTable___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_stdTable___closed__10_value: leanh::LeanStringObject<4> =
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
        m_data: [39, 91, 39, 0],
    };
static mut l_Lake_Toml_stdTable___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_stdTable___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable___closed__23: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_stdTable: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_arrayTable___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [97, 114, 114, 97, 121, 84, 97, 98, 108, 101, 0],
    };
static mut l_Lake_Toml_arrayTable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_arrayTable___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_arrayTable___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_arrayTable___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__0_value)
                as *mut leanh::LeanObject,
            1392117589206424775 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_arrayTable___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_arrayTable___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_arrayTable: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_table___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_table___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_table: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [107, 101, 121, 118, 97, 108, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value)
        as *mut leanh::LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut leanh::LeanObject,
        16525079986463702690 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value)
            as *mut leanh::LeanObject,
        1860500813421358697 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value:
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
    m_data: [101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut leanh::LeanObject,
        16525079986463702690 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value
        ) as *mut leanh::LeanObject,
        17299278796779604842 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_header___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [104, 101, 97, 100, 101, 114, 0],
    };
static mut l_Lake_Toml_header___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_header___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_header___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_header___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_header___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_header___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_header___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_header___closed__0_value)
                as *mut leanh::LeanObject,
            808944059858752425 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_header___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_header___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_header___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_header___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_header: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value:
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
    m_data: [116, 111, 109, 108, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value)
        as *mut leanh::LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut leanh::LeanObject,
        16525079986463702690 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value)
            as *mut leanh::LeanObject,
        4437657283425758961 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value)
            as *mut leanh::LeanObject,
        10608024464111057092 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6_value:
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
    m_data: [108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [105, 110, 108, 105, 110, 101, 84, 97, 98, 108, 101, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut leanh::LeanObject,
        16525079986463702690 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value
        ) as *mut leanh::LeanObject,
        1671555236049616288 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [105, 110, 108, 105, 110, 101, 45, 116, 97, 98, 108, 101, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3_value:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [97, 114, 114, 97, 121, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value)
        as *mut leanh::LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut leanh::LeanObject,
        16525079986463702690 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value)
            as *mut leanh::LeanObject,
        9671799119587300413 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2_value:
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_string___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [115, 116, 114, 105, 110, 103, 0],
    };
static mut l_Lake_Toml_string___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_string___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_string___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_string___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_string___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_string___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_string___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_string___closed__0_value)
                as *mut leanh::LeanObject,
            14667688617378285135 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_string___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_string___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_string___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_string___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_string___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_string___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_string___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_string___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_string___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_string___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_string___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_string___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_string___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_string___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_string___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_string___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_string: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_true___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lake_Toml_true___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_true___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_true___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_true___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_true___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_true___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_true___closed__0_value)
                as *mut leanh::LeanObject,
            5919785301382904414 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_true___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_true___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [39, 116, 114, 117, 101, 39, 0],
    };
static mut l_Lake_Toml_true___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_true___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_true___closed__2_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_true___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_true___closed__4_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_strFn as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_true___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_true___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_true___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_true___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_true___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_true: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_false___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_Toml_false___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_false___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_false___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_false___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_false___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_false___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_false___closed__0_value)
                as *mut leanh::LeanObject,
            4008786854061235757 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_false___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_false___closed__2_value: leanh::LeanStringObject<8> =
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
        m_data: [39, 102, 97, 108, 115, 101, 39, 0],
    };
static mut l_Lake_Toml_false___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_false___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_false___closed__2_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_false___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_false___closed__4_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_strFn as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_false___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_false___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_false___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_false___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_false___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_false: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_boolean___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [98, 111, 111, 108, 101, 97, 110, 0],
    };
static mut l_Lake_Toml_boolean___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_boolean___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_boolean___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_boolean___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_boolean___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_boolean___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_boolean___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_boolean___closed__0_value)
                as *mut leanh::LeanObject,
            8637345244662348 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_boolean___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_boolean___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_boolean___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_boolean___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_boolean___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_boolean___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_boolean: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Toml_numeralAntiquot___closed__6_value: leanh::LeanStringObject<8> =
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
        m_data: [110, 117, 109, 101, 114, 97, 108, 0],
    };
static mut l_Lake_Toml_numeralAntiquot___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lake_Toml_numeralAntiquot___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_numeralAntiquot___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_numeralAntiquot___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__6_value)
                as *mut leanh::LeanObject,
            2769446217552894055 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_numeralAntiquot___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Toml_numeralAntiquot___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeralAntiquot___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_numeralAntiquot: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeral___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeral___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeral___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_numeral___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_numeral: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_numeralOfKind___closed__0_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            105, 108, 108, 101, 103, 97, 108, 32, 110, 117, 109, 101, 114, 97, 108, 32, 107, 105,
            110, 100, 0,
        ],
    };
static mut l_Lake_Toml_numeralOfKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralOfKind___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_Toml_float___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_float___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_float: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_decInt___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_decInt___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_decInt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_binNum___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            98, 105, 110, 97, 114, 121, 32, 110, 117, 109, 98, 101, 114, 0,
        ],
    };
static mut l_Lake_Toml_binNum___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_binNum___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_binNum___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_binNum___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_binNum: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_octNum___closed__0_value: leanh::LeanStringObject<13> =
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
        m_data: [111, 99, 116, 97, 108, 32, 110, 117, 109, 98, 101, 114, 0],
    };
static mut l_Lake_Toml_octNum___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_octNum___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_octNum___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_octNum___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_octNum: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_hexNum___closed__0_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            104, 101, 120, 97, 100, 101, 99, 105, 109, 97, 108, 32, 110, 117, 109, 98, 101, 114, 0,
        ],
    };
static mut l_Lake_Toml_hexNum___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_hexNum___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_hexNum___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_hexNum___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_hexNum: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_dateTime___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_dateTime___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_dateTime: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_val___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [118, 97, 108, 0],
    };
static mut l_Lake_Toml_val___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_val___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_Toml_val___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_Toml_val___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_val___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut leanh::LeanObject,
            16525079986463702690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_val___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_val___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_val___closed__0_value) as *mut leanh::LeanObject,
            16311065367698350545 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_val___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_val___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Toml_val___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_val___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_val___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_Toml_val___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_val___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_val: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_array___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_array___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_array: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_inlineTable___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_inlineTable___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_inlineTable: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_keyval___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_keyval___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_keyval: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_expression___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_expression___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_expression: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_simpleKey_formatter___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_simpleKey_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_key_formatter___closed__0___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_formatter___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_formatter___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_formatter___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_formatter___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_formatter___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_formatter___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_formatter___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_formatter___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_formatter___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lake_Toml_simpleKey_parenthesizer___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_simpleKey_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_parenthesizer___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_key_parenthesizer___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_stdTable_parenthesizer___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0_value: leanh::LeanClosureObject<4> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 4, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lake_Toml_toml___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_toml___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_toml___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_toml___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_toml: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lake_Toml_isControlChar(mut v_c_2840_: u32) -> u8 {
    let mut v___x_2841_: u32 = 0;
    let mut v___x_2842_: u8 = 0;
    v___x_2841_ = 127;
    v___x_2842_ = lean_uint32_dec_eq(v_c_2840_, v___x_2841_);
    if v___x_2842_ == 0 {
        let mut v___x_2843_: u32 = 0;
        let mut v___x_2844_: u8 = 0;
        v___x_2843_ = 32;
        v___x_2844_ = lean_uint32_dec_lt(v_c_2840_, v___x_2843_);
        if v___x_2844_ == 0 {
            return v___x_2844_;
        } else {
            let mut v___x_2845_: u32 = 0;
            let mut v___x_2846_: u8 = 0;
            v___x_2845_ = 9;
            v___x_2846_ = lean_uint32_dec_eq(v_c_2840_, v___x_2845_);
            if v___x_2846_ == 0 {
                return v___x_2844_;
            } else {
                return v___x_2842_;
            }
        }
    } else {
        return v___x_2842_;
    }
}
pub unsafe fn l_Lake_Toml_isControlChar___boxed(
    mut v_c_2847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2848_: u32 = 0;
    let mut v_res_2849_: u8 = 0;
    let mut v_r_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2848_ = leanh::lean_unbox_uint32(v_c_2847_);
    leanh::lean_dec(v_c_2847_);
    v_res_2849_ = l_Lake_Toml_isControlChar(v_c_boxed_2848_);
    v_r_2850_ = leanh::lean_box((v_res_2849_) as usize);
    return v_r_2850_;
}
pub unsafe fn l_Lake_Toml_wsFn___lam__0(mut v_c_2851_: u32) -> u8 {
    let mut v___x_2852_: u32 = 0;
    let mut v___x_2853_: u8 = 0;
    v___x_2852_ = 32;
    v___x_2853_ = lean_uint32_dec_eq(v_c_2851_, v___x_2852_);
    if v___x_2853_ == 0 {
        let mut v___x_2854_: u32 = 0;
        let mut v___x_2855_: u8 = 0;
        v___x_2854_ = 9;
        v___x_2855_ = lean_uint32_dec_eq(v_c_2851_, v___x_2854_);
        return v___x_2855_;
    } else {
        return v___x_2853_;
    }
}
pub unsafe fn l_Lake_Toml_wsFn___lam__0___boxed(
    mut v_c_2856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2857_: u32 = 0;
    let mut v_res_2858_: u8 = 0;
    let mut v_r_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2857_ = leanh::lean_unbox_uint32(v_c_2856_);
    leanh::lean_dec(v_c_2856_);
    v_res_2858_ = l_Lake_Toml_wsFn___lam__0(v_c_boxed_2857_);
    v_r_2859_ = leanh::lean_box((v_res_2858_) as usize);
    return v_r_2859_;
}
pub unsafe fn l_Lake_Toml_wsFn(
    mut v_a_2861_: *mut leanh::LeanObject,
    mut v_a_2862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2863_ = l_Lake_Toml_wsFn___closed__0;
    v___x_2864_ = l_Lean_Parser_takeWhileFn(v___f_2863_, v_a_2861_, v_a_2862_);
    return v___x_2864_;
}
pub unsafe fn l_Lake_Toml_wsFn___boxed(
    mut v_a_2865_: *mut leanh::LeanObject,
    mut v_a_2866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2867_ = l_Lake_Toml_wsFn(v_a_2865_, v_a_2866_);
    leanh::lean_dec_ref(v_a_2865_);
    return v_res_2867_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
    mut v_c_2869_: *mut leanh::LeanObject,
    mut v_s_2870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errMsg_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: u8 = 0;
    v_toInputContext_2871_ = leanh::lean_ctor_get(v_c_2869_, 0);
    v_pos_2872_ = leanh::lean_ctor_get(v_s_2870_, 2);
    v_errMsg_2873_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0;
    v___x_2874_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2871_, v_pos_2872_);
    v___x_2875_ = 1;
    if v___x_2874_ == 0 {
        let mut v_inputString_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_curr_2877_: u32 = 0;
        let mut v___x_2878_: u32 = 0;
        let mut v___x_2879_: u8 = 0;
        v_inputString_2876_ = leanh::lean_ctor_get(v_toInputContext_2871_, 0);
        v_curr_2877_ = lean_string_utf8_get_fast(v_inputString_2876_, v_pos_2872_);
        v___x_2878_ = 10;
        v___x_2879_ = lean_uint32_dec_eq(v_curr_2877_, v___x_2878_);
        if v___x_2879_ == 0 {
            let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2880_ = leanh::lean_box(0);
            v___x_2881_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                v_s_2870_,
                v_errMsg_2873_,
                v___x_2880_,
                v___x_2875_,
            );
            return v___x_2881_;
        } else {
            let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_pos_2872_);
            v___x_2882_ =
                l_Lean_Parser_ParserState_next_x27___redArg(v_s_2870_, v_c_2869_, v_pos_2872_);
            leanh::lean_dec(v_pos_2872_);
            return v___x_2882_;
        }
    } else {
        let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2883_ = leanh::lean_box(0);
        v___x_2884_ = l_Lean_Parser_ParserState_mkUnexpectedError(
            v_s_2870_,
            v_errMsg_2873_,
            v___x_2883_,
            v___x_2875_,
        );
        return v___x_2884_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___boxed(
    mut v_c_2885_: *mut leanh::LeanObject,
    mut v_s_2886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2887_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_2885_, v_s_2886_);
    leanh::lean_dec_ref(v_c_2885_);
    return v_res_2887_;
}
pub unsafe fn l_Lake_Toml_newlineFn(
    mut v_c_2892_: *mut leanh::LeanObject,
    mut v_s_2893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: u8 = 0;
    v_toInputContext_2894_ = leanh::lean_ctor_get(v_c_2892_, 0);
    v_pos_2895_ = leanh::lean_ctor_get(v_s_2893_, 2);
    v___x_2896_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2894_, v_pos_2895_);
    if v___x_2896_ == 0 {
        let mut v_inputString_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_curr_2898_: u32 = 0;
        let mut v___x_2899_: u32 = 0;
        let mut v___x_2900_: u8 = 0;
        v_inputString_2897_ = leanh::lean_ctor_get(v_toInputContext_2894_, 0);
        v_curr_2898_ = lean_string_utf8_get_fast(v_inputString_2897_, v_pos_2895_);
        v___x_2899_ = 10;
        v___x_2900_ = lean_uint32_dec_eq(v_curr_2898_, v___x_2899_);
        if v___x_2900_ == 0 {
            let mut v___x_2901_: u32 = 0;
            let mut v___x_2902_: u8 = 0;
            v___x_2901_ = 13;
            v___x_2902_ = lean_uint32_dec_eq(v_curr_2898_, v___x_2901_);
            if v___x_2902_ == 0 {
                let mut v___x_2903_: u8 = 0;
                let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2903_ = 1;
                v___x_2904_ = l_Lake_Toml_newlineFn___closed__1;
                v___x_2905_ = l_Lake_Toml_mkUnexpectedCharError(
                    v_s_2893_,
                    v_curr_2898_,
                    v___x_2904_,
                    v___x_2903_,
                );
                return v___x_2905_;
            } else {
                let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_pos_2895_);
                v___x_2906_ =
                    l_Lean_Parser_ParserState_next_x27___redArg(v_s_2893_, v_c_2892_, v_pos_2895_);
                leanh::lean_dec(v_pos_2895_);
                v___x_2907_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_2892_, v___x_2906_);
                return v___x_2907_;
            }
        } else {
            let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_pos_2895_);
            v___x_2908_ =
                l_Lean_Parser_ParserState_next_x27___redArg(v_s_2893_, v_c_2892_, v_pos_2895_);
            leanh::lean_dec(v_pos_2895_);
            return v___x_2908_;
        }
    } else {
        let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2909_ = l_Lake_Toml_newlineFn___closed__1;
        v___x_2910_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2893_, v___x_2909_);
        return v___x_2910_;
    }
}
pub unsafe fn l_Lake_Toml_newlineFn___boxed(
    mut v_c_2911_: *mut leanh::LeanObject,
    mut v_s_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2913_ = l_Lake_Toml_newlineFn(v_c_2911_, v_s_2912_);
    leanh::lean_dec_ref(v_c_2911_);
    return v_res_2913_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(
    mut v_a_2915_: *mut leanh::LeanObject,
    mut v_a_2916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0;
    v___x_2918_ = l_Lean_Parser_takeUntilFn(v___x_2917_, v_a_2915_, v_a_2916_);
    return v___x_2918_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___boxed(
    mut v_a_2919_: *mut leanh::LeanObject,
    mut v_a_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_2919_, v_a_2920_);
    leanh::lean_dec_ref(v_a_2919_);
    return v_res_2921_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
    mut v_x_2922_: *mut leanh::LeanObject,
    mut v_x_2923_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2922_) == 0 {
        if leanh::lean_obj_tag(v_x_2923_) == 0 {
            let mut v___x_2924_: u8 = 0;
            v___x_2924_ = 1;
            return v___x_2924_;
        } else {
            let mut v___x_2925_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_2923_, 1);
            v___x_2925_ = 0;
            return v___x_2925_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_2923_) == 0 {
            let mut v___x_2926_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_2922_, 1);
            v___x_2926_ = 0;
            return v___x_2926_;
        } else {
            let mut v_val_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2929_: u8 = 0;
            v_val_2927_ = leanh::lean_ctor_get(v_x_2922_, 0);
            leanh::lean_inc(v_val_2927_);
            leanh::lean_dec_ref_known(v_x_2922_, 1);
            v_val_2928_ = leanh::lean_ctor_get(v_x_2923_, 0);
            leanh::lean_inc(v_val_2928_);
            leanh::lean_dec_ref_known(v_x_2923_, 1);
            v___x_2929_ = l_Lean_Parser_instBEqError_beq(v_val_2927_, v_val_2928_);
            return v___x_2929_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0___boxed(
    mut v_x_2930_: *mut leanh::LeanObject,
    mut v_x_2931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2932_: u8 = 0;
    let mut v_r_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_x_2930_, v_x_2931_);
    v_r_2933_ = leanh::lean_box((v_res_2932_) as usize);
    return v_r_2933_;
}
pub unsafe fn l_Lake_Toml_commentFn(
    mut v_a_2938_: *mut leanh::LeanObject,
    mut v_a_2939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2940_: u32 = 0;
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: u8 = 0;
    v___x_2940_ = 35;
    v___x_2941_ = l_Lake_Toml_commentFn___closed__1;
    v_s_2942_ = l_Lake_Toml_chFn(v___x_2940_, v___x_2941_, v_a_2938_, v_a_2939_);
    v_errorMsg_2943_ = leanh::lean_ctor_get(v_s_2942_, 4);
    leanh::lean_inc(v_errorMsg_2943_);
    v___x_2944_ = leanh::lean_box(0);
    v___x_2945_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_2943_, v___x_2944_);
    if v___x_2945_ == 0 {
        return v_s_2942_;
    } else {
        let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2946_ =
            l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_2938_, v_s_2942_);
        return v___x_2946_;
    }
}
pub unsafe fn l_Lake_Toml_commentFn___boxed(
    mut v_a_2947_: *mut leanh::LeanObject,
    mut v_a_2948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_Lake_Toml_commentFn(v_a_2947_, v_a_2948_);
    leanh::lean_dec_ref(v_a_2947_);
    return v_res_2949_;
}
pub unsafe fn l_Lake_Toml_wsNewlineFn(
    mut v_c_2950_: *mut leanh::LeanObject,
    mut v_s_2951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v_inputString_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_2959_: u32 = 0;
    let mut v___y_2961_: u8 = 0;
    let mut v___x_2962_: u32 = 0;
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: u32 = 0;
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2972_: u32 = 0;
    let mut v___x_2973_: u8 = 0;
    let mut v___x_2974_: u32 = 0;
    let mut v___x_2975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_2952_ = leanh::lean_ctor_get(v_c_2950_, 0);
                v_pos_2953_ = leanh::lean_ctor_get(v_s_2951_, 2);
                v___x_2957_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2952_, v_pos_2953_);
                if v___x_2957_ == 0 {
                    v_inputString_2958_ = leanh::lean_ctor_get(v_toInputContext_2952_, 0);
                    v_curr_2959_ = lean_string_utf8_get_fast(v_inputString_2958_, v_pos_2953_);
                    v___x_2972_ = 32;
                    v___x_2973_ = lean_uint32_dec_eq(v_curr_2959_, v___x_2972_);
                    if v___x_2973_ == 0 {
                        v___x_2974_ = 9;
                        v___x_2975_ = lean_uint32_dec_eq(v_curr_2959_, v___x_2974_);
                        v___y_2961_ = v___x_2975_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2961_ = v___x_2973_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_s_2951_;
                }
            }
            1 => {
                v___x_2955_ =
                    l_Lean_Parser_ParserState_next_x27___redArg(v_s_2951_, v_c_2950_, v_pos_2953_);
                leanh::lean_dec(v_pos_2953_);
                v_s_2951_ = v___x_2955_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2961_ == 0 {
                    v___x_2962_ = 10;
                    v___x_2963_ = lean_uint32_dec_eq(v_curr_2959_, v___x_2962_);
                    if v___x_2963_ == 0 {
                        v___x_2964_ = 13;
                        v___x_2965_ = lean_uint32_dec_eq(v_curr_2959_, v___x_2964_);
                        if v___x_2965_ == 0 {
                            return v_s_2951_;
                        } else {
                            leanh::lean_inc(v_pos_2953_);
                            v___x_2966_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_2951_,
                                v_c_2950_,
                                v_pos_2953_,
                            );
                            leanh::lean_dec(v_pos_2953_);
                            v_s_2967_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
                                v_c_2950_,
                                v___x_2966_,
                            );
                            v_errorMsg_2968_ = leanh::lean_ctor_get(v_s_2967_, 4);
                            leanh::lean_inc(v_errorMsg_2968_);
                            v___x_2969_ = leanh::lean_box(0);
                            v___x_2970_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                v_errorMsg_2968_,
                                v___x_2969_,
                            );
                            if v___x_2970_ == 0 {
                                return v_s_2967_;
                            } else {
                                v_s_2951_ = v_s_2967_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_inc(v_pos_2953_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_pos_2953_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_wsNewlineFn___boxed(
    mut v_c_2976_: *mut leanh::LeanObject,
    mut v_s_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lake_Toml_wsNewlineFn(v_c_2976_, v_s_2977_);
    leanh::lean_dec_ref(v_c_2976_);
    return v_res_2978_;
}
pub unsafe fn l_Lake_Toml_trailingFn(
    mut v_c_2979_: *mut leanh::LeanObject,
    mut v_s_2980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v_inputString_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_2988_: u32 = 0;
    let mut v___y_2990_: u8 = 0;
    let mut v___x_2991_: u32 = 0;
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: u32 = 0;
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: u32 = 0;
    let mut v___x_2996_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: u8 = 0;
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3009_: u32 = 0;
    let mut v___x_3010_: u8 = 0;
    let mut v___x_3011_: u32 = 0;
    let mut v___x_3012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_2981_ = leanh::lean_ctor_get(v_c_2979_, 0);
                v_pos_2982_ = leanh::lean_ctor_get(v_s_2980_, 2);
                v___x_2986_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2981_, v_pos_2982_);
                if v___x_2986_ == 0 {
                    v_inputString_2987_ = leanh::lean_ctor_get(v_toInputContext_2981_, 0);
                    v_curr_2988_ = lean_string_utf8_get_fast(v_inputString_2987_, v_pos_2982_);
                    v___x_3009_ = 32;
                    v___x_3010_ = lean_uint32_dec_eq(v_curr_2988_, v___x_3009_);
                    if v___x_3010_ == 0 {
                        v___x_3011_ = 9;
                        v___x_3012_ = lean_uint32_dec_eq(v_curr_2988_, v___x_3011_);
                        v___y_2990_ = v___x_3012_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2990_ = v___x_3010_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_s_2980_;
                }
            }
            1 => {
                v___x_2984_ =
                    l_Lean_Parser_ParserState_next_x27___redArg(v_s_2980_, v_c_2979_, v_pos_2982_);
                leanh::lean_dec(v_pos_2982_);
                v_s_2980_ = v___x_2984_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2990_ == 0 {
                    v___x_2991_ = 10;
                    v___x_2992_ = lean_uint32_dec_eq(v_curr_2988_, v___x_2991_);
                    if v___x_2992_ == 0 {
                        v___x_2993_ = 13;
                        v___x_2994_ = lean_uint32_dec_eq(v_curr_2988_, v___x_2993_);
                        if v___x_2994_ == 0 {
                            v___x_2995_ = 35;
                            v___x_2996_ = lean_uint32_dec_eq(v_curr_2988_, v___x_2995_);
                            if v___x_2996_ == 0 {
                                return v_s_2980_;
                            } else {
                                leanh::lean_inc(v_pos_2982_);
                                v___x_2997_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_2980_,
                                    v_c_2979_,
                                    v_pos_2982_,
                                );
                                leanh::lean_dec(v_pos_2982_);
                                v_s_2998_ =
                                    l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(
                                        v_c_2979_,
                                        v___x_2997_,
                                    );
                                v_errorMsg_2999_ = leanh::lean_ctor_get(v_s_2998_, 4);
                                leanh::lean_inc(v_errorMsg_2999_);
                                v___x_3000_ = leanh::lean_box(0);
                                v___x_3001_ =
                                    l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                        v_errorMsg_2999_,
                                        v___x_3000_,
                                    );
                                if v___x_3001_ == 0 {
                                    return v_s_2998_;
                                } else {
                                    v_s_2980_ = v_s_2998_;
                                    state = 0;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_inc(v_pos_2982_);
                            v___x_3003_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_2980_,
                                v_c_2979_,
                                v_pos_2982_,
                            );
                            leanh::lean_dec(v_pos_2982_);
                            v_s_3004_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
                                v_c_2979_,
                                v___x_3003_,
                            );
                            v_errorMsg_3005_ = leanh::lean_ctor_get(v_s_3004_, 4);
                            leanh::lean_inc(v_errorMsg_3005_);
                            v___x_3006_ = leanh::lean_box(0);
                            v___x_3007_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                v_errorMsg_3005_,
                                v___x_3006_,
                            );
                            if v___x_3007_ == 0 {
                                return v_s_3004_;
                            } else {
                                v_s_2980_ = v_s_3004_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_inc(v_pos_2982_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_pos_2982_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_trailingFn___boxed(
    mut v_c_3013_: *mut leanh::LeanObject,
    mut v_s_3014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3015_ = l_Lake_Toml_trailingFn(v_c_3013_, v_s_3014_);
    leanh::lean_dec_ref(v_c_3013_);
    return v_res_3015_;
}
pub unsafe fn l_Lake_Toml_isEscapeChar(mut v_c_3016_: u32) -> u8 {
    let mut v___y_3018_: u8 = 0;
    let mut v___x_3019_: u32 = 0;
    let mut v___x_3020_: u8 = 0;
    let mut v___x_3021_: u32 = 0;
    let mut v___x_3022_: u8 = 0;
    let mut v___x_3023_: u32 = 0;
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: u32 = 0;
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: u32 = 0;
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: u32 = 0;
    let mut v___x_3030_: u8 = 0;
    let mut v___x_3031_: u32 = 0;
    let mut v___x_3032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3029_ = 98;
                v___x_3030_ = lean_uint32_dec_eq(v_c_3016_, v___x_3029_);
                if v___x_3030_ == 0 {
                    v___x_3031_ = 116;
                    v___x_3032_ = lean_uint32_dec_eq(v_c_3016_, v___x_3031_);
                    v___y_3018_ = v___x_3032_;
                    state = 1;
                    continue;
                } else {
                    v___y_3018_ = v___x_3030_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3018_ == 0 {
                    v___x_3019_ = 110;
                    v___x_3020_ = lean_uint32_dec_eq(v_c_3016_, v___x_3019_);
                    if v___x_3020_ == 0 {
                        v___x_3021_ = 102;
                        v___x_3022_ = lean_uint32_dec_eq(v_c_3016_, v___x_3021_);
                        if v___x_3022_ == 0 {
                            v___x_3023_ = 114;
                            v___x_3024_ = lean_uint32_dec_eq(v_c_3016_, v___x_3023_);
                            if v___x_3024_ == 0 {
                                v___x_3025_ = 34;
                                v___x_3026_ = lean_uint32_dec_eq(v_c_3016_, v___x_3025_);
                                if v___x_3026_ == 0 {
                                    v___x_3027_ = 92;
                                    v___x_3028_ = lean_uint32_dec_eq(v_c_3016_, v___x_3027_);
                                    return v___x_3028_;
                                } else {
                                    return v___x_3026_;
                                }
                            } else {
                                return v___x_3024_;
                            }
                        } else {
                            return v___x_3022_;
                        }
                    } else {
                        return v___x_3020_;
                    }
                } else {
                    return v___y_3018_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_isEscapeChar___boxed(
    mut v_c_3033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_3034_: u32 = 0;
    let mut v_res_3035_: u8 = 0;
    let mut v_r_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_3034_ = leanh::lean_unbox_uint32(v_c_3033_);
    leanh::lean_dec(v_c_3033_);
    v_res_3035_ = l_Lake_Toml_isEscapeChar(v_c_boxed_3034_);
    v_r_3036_ = leanh::lean_box((v_res_3035_) as usize);
    return v_r_3036_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(
    mut v___y_3037_: *mut leanh::LeanObject,
    mut v___y_3038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    v_s_3039_ = l_Lake_Toml_wsFn(v___y_3037_, v___y_3038_);
    v_errorMsg_3040_ = leanh::lean_ctor_get(v_s_3039_, 4);
    leanh::lean_inc(v_errorMsg_3040_);
    v___x_3041_ = leanh::lean_box(0);
    v___x_3042_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3040_, v___x_3041_);
    if v___x_3042_ == 0 {
        return v_s_3039_;
    } else {
        let mut v_s_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3045_: u8 = 0;
        v_s_3043_ = l_Lake_Toml_newlineFn(v___y_3037_, v_s_3039_);
        v_errorMsg_3044_ = leanh::lean_ctor_get(v_s_3043_, 4);
        leanh::lean_inc(v_errorMsg_3044_);
        v___x_3045_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3044_,
            v___x_3041_,
        );
        if v___x_3045_ == 0 {
            return v_s_3043_;
        } else {
            let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3046_ = l_Lake_Toml_wsNewlineFn(v___y_3037_, v_s_3043_);
            return v___x_3046_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(
    mut v___y_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3049_ =
        l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(v___y_3047_, v___y_3048_);
    leanh::lean_dec_ref(v___y_3047_);
    return v_res_3049_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(
    mut v___y_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u8 = 0;
    v_s_3052_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v___y_3050_, v___y_3051_);
    v_errorMsg_3053_ = leanh::lean_ctor_get(v_s_3052_, 4);
    leanh::lean_inc(v_errorMsg_3053_);
    v___x_3054_ = leanh::lean_box(0);
    v___x_3055_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3053_, v___x_3054_);
    if v___x_3055_ == 0 {
        return v_s_3052_;
    } else {
        let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3056_ = l_Lake_Toml_wsNewlineFn(v___y_3050_, v_s_3052_);
        return v___x_3056_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(
    mut v___y_3057_: *mut leanh::LeanObject,
    mut v___y_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ =
        l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(v___y_3057_, v___y_3058_);
    leanh::lean_dec_ref(v___y_3057_);
    return v_res_3059_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(
    mut v_c_3060_: *mut leanh::LeanObject,
    mut v_x_3061_: *mut leanh::LeanObject,
    mut v_x_3062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3064_: u8 = 0;
    let mut v_s_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v_one_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3063_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3064_ = lean_nat_dec_eq(v_x_3061_, v_zero_3063_);
                if v_isZero_3064_ == 1 {
                    leanh::lean_dec(v_x_3061_);
                    return v_x_3062_;
                } else {
                    v_s_3065_ = l_Lean_Parser_hexDigitFn(v_c_3060_, v_x_3062_);
                    v_errorMsg_3066_ = leanh::lean_ctor_get(v_s_3065_, 4);
                    leanh::lean_inc(v_errorMsg_3066_);
                    v___x_3067_ = leanh::lean_box(0);
                    v___x_3068_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3066_,
                        v___x_3067_,
                    );
                    if v___x_3068_ == 0 {
                        leanh::lean_dec(v_x_3061_);
                        return v_s_3065_;
                    } else {
                        v_one_3069_ = leanh::lean_unsigned_to_nat(1);
                        v_n_3070_ = lean_nat_sub(v_x_3061_, v_one_3069_);
                        leanh::lean_dec(v_x_3061_);
                        v_x_3061_ = v_n_3070_;
                        v_x_3062_ = v_s_3065_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0___boxed(
    mut v_c_3072_: *mut leanh::LeanObject,
    mut v_x_3073_: *mut leanh::LeanObject,
    mut v_x_3074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3075_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_3072_, v_x_3073_, v_x_3074_);
    leanh::lean_dec_ref(v_c_3072_);
    return v_res_3075_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(
    mut v_stringGap_3085_: u8,
    mut v_c_3086_: *mut leanh::LeanObject,
    mut v_s_3087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: u8 = 0;
    let mut v_inputString_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3094_: u32 = 0;
    let mut v___x_3095_: u8 = 0;
    let mut v___x_3096_: u32 = 0;
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: u32 = 0;
    let mut v___x_3099_: u8 = 0;
    let mut v___f_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v_p_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u32 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: u32 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: u32 = 0;
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: u32 = 0;
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3088_ = leanh::lean_ctor_get(v_c_3086_, 0);
                v_pos_3089_ = leanh::lean_ctor_get(v_s_3087_, 2);
                v___x_3090_ = leanh::lean_box(0);
                v_expected_3091_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1;
                v___x_3092_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3088_, v_pos_3089_);
                if v___x_3092_ == 0 {
                    v_inputString_3093_ = leanh::lean_ctor_get(v_toInputContext_3088_, 0);
                    v_curr_3094_ = lean_string_utf8_get_fast(v_inputString_3093_, v_pos_3089_);
                    v___x_3095_ = l_Lake_Toml_isEscapeChar(v_curr_3094_);
                    if v___x_3095_ == 0 {
                        v___x_3096_ = 117;
                        v___x_3097_ = lean_uint32_dec_eq(v_curr_3094_, v___x_3096_);
                        if v___x_3097_ == 0 {
                            v___x_3098_ = 85;
                            v___x_3099_ = lean_uint32_dec_eq(v_curr_3094_, v___x_3098_);
                            if v___x_3099_ == 0 {
                                v___f_3100_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2;
                                v___x_3101_ = 1;
                                v___x_3108_ = 32;
                                v___x_3109_ = lean_uint32_dec_eq(v_curr_3094_, v___x_3108_);
                                if v___x_3109_ == 0 {
                                    v___x_3110_ = 9;
                                    v___x_3111_ = lean_uint32_dec_eq(v_curr_3094_, v___x_3110_);
                                    if v___x_3111_ == 0 {
                                        v___x_3112_ = 10;
                                        v___x_3113_ = lean_uint32_dec_eq(v_curr_3094_, v___x_3112_);
                                        if v___x_3113_ == 0 {
                                            v___x_3114_ = 13;
                                            v___x_3115_ =
                                                lean_uint32_dec_eq(v_curr_3094_, v___x_3114_);
                                            if v___x_3115_ == 0 {
                                                leanh::lean_dec_ref(v_c_3086_);
                                                v___x_3116_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4;
                                                v___x_3117_ =
                                                    l_Lean_Parser_ParserState_mkUnexpectedError(
                                                        v_s_3087_,
                                                        v___x_3116_,
                                                        v___x_3090_,
                                                        v___x_3101_,
                                                    );
                                                return v___x_3117_;
                                            } else {
                                                v___f_3118_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5;
                                                v_p_3103_ = v___f_3118_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___x_3119_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6;
                                            v_p_3103_ = v___x_3119_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v_p_3103_ = v___f_3100_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_p_3103_ = v___f_3100_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_inc(v_pos_3089_);
                                v___x_3120_ = leanh::lean_unsigned_to_nat(8);
                                v___x_3121_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_3087_,
                                    v_c_3086_,
                                    v_pos_3089_,
                                );
                                leanh::lean_dec(v_pos_3089_);
                                v___x_3122_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_3086_, v___x_3120_, v___x_3121_);
                                leanh::lean_dec_ref(v_c_3086_);
                                return v___x_3122_;
                            }
                        } else {
                            leanh::lean_inc(v_pos_3089_);
                            v___x_3123_ = leanh::lean_unsigned_to_nat(4);
                            v___x_3124_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_3087_,
                                v_c_3086_,
                                v_pos_3089_,
                            );
                            leanh::lean_dec(v_pos_3089_);
                            v___x_3125_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_3086_, v___x_3123_, v___x_3124_);
                            leanh::lean_dec_ref(v_c_3086_);
                            return v___x_3125_;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3089_);
                        v___x_3126_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3087_,
                            v_c_3086_,
                            v_pos_3089_,
                        );
                        leanh::lean_dec(v_pos_3089_);
                        leanh::lean_dec_ref(v_c_3086_);
                        return v___x_3126_;
                    }
                } else {
                    leanh::lean_dec_ref(v_c_3086_);
                    v___x_3127_ = l_Lean_Parser_ParserState_mkEOIError(v_s_3087_, v_expected_3091_);
                    return v___x_3127_;
                }
            }
            1 => {
                if v_stringGap_3085_ == 0 {
                    leanh::lean_dec_ref(v_c_3086_);
                    v___x_3104_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3;
                    v___x_3105_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                        v_s_3087_,
                        v___x_3104_,
                        v_expected_3091_,
                        v___x_3101_,
                    );
                    return v___x_3105_;
                } else {
                    leanh::lean_inc(v_pos_3089_);
                    v___x_3106_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3087_,
                        v_c_3086_,
                        v_pos_3089_,
                    );
                    leanh::lean_dec(v_pos_3089_);
                    leanh::lean_inc_ref(v_p_3103_);
                    v___x_3107_ = leanh::lean_apply_2(v_p_3103_, v_c_3086_, v___x_3106_);
                    return v___x_3107_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(
    mut v_stringGap_3128_: *mut leanh::LeanObject,
    mut v_c_3129_: *mut leanh::LeanObject,
    mut v_s_3130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stringGap_boxed_3131_: u8 = 0;
    let mut v_res_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stringGap_boxed_3131_ = (leanh::lean_unbox(v_stringGap_3128_) as u8);
    v_res_3132_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(
        v_stringGap_boxed_3131_,
        v_c_3129_,
        v_s_3130_,
    );
    return v_res_3132_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(
    mut v_startPos_3134_: *mut leanh::LeanObject,
    mut v_c_3135_: *mut leanh::LeanObject,
    mut v_s_3136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v_inputString_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3141_: u32 = 0;
    let mut v___x_3142_: u32 = 0;
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: u32 = 0;
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: u8 = 0;
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: u8 = 0;
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3137_ = leanh::lean_ctor_get(v_c_3135_, 0);
                v_pos_3138_ = leanh::lean_ctor_get(v_s_3136_, 2);
                v___x_3139_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3137_, v_pos_3138_);
                if v___x_3139_ == 0 {
                    v_inputString_3140_ = leanh::lean_ctor_get(v_toInputContext_3137_, 0);
                    v_curr_3141_ = lean_string_utf8_get_fast(v_inputString_3140_, v_pos_3138_);
                    v___x_3142_ = 34;
                    v___x_3143_ = lean_uint32_dec_eq(v_curr_3141_, v___x_3142_);
                    if v___x_3143_ == 0 {
                        v___x_3144_ = 92;
                        v___x_3145_ = lean_uint32_dec_eq(v_curr_3141_, v___x_3144_);
                        if v___x_3145_ == 0 {
                            v___x_3146_ = l_Lake_Toml_isControlChar(v_curr_3141_);
                            if v___x_3146_ == 0 {
                                leanh::lean_inc(v_pos_3138_);
                                v___x_3147_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_3136_,
                                    v_c_3135_,
                                    v_pos_3138_,
                                );
                                leanh::lean_dec(v_pos_3138_);
                                v_s_3136_ = v___x_3147_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_c_3135_);
                                leanh::lean_dec(v_startPos_3134_);
                                v___x_3149_ = leanh::lean_box(0);
                                v___x_3150_ = l_Lake_Toml_mkUnexpectedCharError(
                                    v_s_3136_,
                                    v_curr_3141_,
                                    v___x_3149_,
                                    v___x_3146_,
                                );
                                return v___x_3150_;
                            }
                        } else {
                            leanh::lean_inc(v_pos_3138_);
                            v___x_3151_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_3136_,
                                v_c_3135_,
                                v_pos_3138_,
                            );
                            leanh::lean_dec(v_pos_3138_);
                            leanh::lean_inc_ref(v_c_3135_);
                            v_s_3152_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(
                                v___x_3143_,
                                v_c_3135_,
                                v___x_3151_,
                            );
                            v_errorMsg_3153_ = leanh::lean_ctor_get(v_s_3152_, 4);
                            leanh::lean_inc(v_errorMsg_3153_);
                            v___x_3154_ = leanh::lean_box(0);
                            v___x_3155_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                v_errorMsg_3153_,
                                v___x_3154_,
                            );
                            if v___x_3155_ == 0 {
                                leanh::lean_dec_ref(v_c_3135_);
                                leanh::lean_dec(v_startPos_3134_);
                                return v_s_3152_;
                            } else {
                                v_s_3136_ = v_s_3152_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_inc(v_pos_3138_);
                        leanh::lean_dec(v_startPos_3134_);
                        v___x_3157_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3136_,
                            v_c_3135_,
                            v_pos_3138_,
                        );
                        leanh::lean_dec(v_pos_3138_);
                        leanh::lean_dec_ref(v_c_3135_);
                        return v___x_3157_;
                    }
                } else {
                    leanh::lean_dec_ref(v_c_3135_);
                    v___x_3158_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0;
                    v___x_3159_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(
                        v_s_3136_,
                        v___x_3158_,
                        v_startPos_3134_,
                    );
                    return v___x_3159_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_basicStringFn(
    mut v_a_3164_: *mut leanh::LeanObject,
    mut v_a_3165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: u32 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    v_pos_3166_ = leanh::lean_ctor_get(v_a_3165_, 2);
    leanh::lean_inc(v_pos_3166_);
    v___x_3167_ = 34;
    v___x_3168_ = l_Lake_Toml_basicStringFn___closed__1;
    v_s_3169_ = l_Lake_Toml_chFn(v___x_3167_, v___x_3168_, v_a_3164_, v_a_3165_);
    v_errorMsg_3170_ = leanh::lean_ctor_get(v_s_3169_, 4);
    leanh::lean_inc(v_errorMsg_3170_);
    v___x_3171_ = leanh::lean_box(0);
    v___x_3172_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3170_, v___x_3171_);
    if v___x_3172_ == 0 {
        leanh::lean_dec(v_pos_3166_);
        leanh::lean_dec_ref(v_a_3164_);
        return v_s_3169_;
    } else {
        let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3173_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(
            v_pos_3166_,
            v_a_3164_,
            v_s_3169_,
        );
        return v___x_3173_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(
    mut v_startPos_3175_: *mut leanh::LeanObject,
    mut v_c_3176_: *mut leanh::LeanObject,
    mut v_s_3177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: u8 = 0;
    let mut v_inputString_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3182_: u32 = 0;
    let mut v___x_3183_: u32 = 0;
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: u8 = 0;
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3178_ = leanh::lean_ctor_get(v_c_3176_, 0);
                v_pos_3179_ = leanh::lean_ctor_get(v_s_3177_, 2);
                v___x_3180_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3178_, v_pos_3179_);
                if v___x_3180_ == 0 {
                    v_inputString_3181_ = leanh::lean_ctor_get(v_toInputContext_3178_, 0);
                    v_curr_3182_ = lean_string_utf8_get_fast(v_inputString_3181_, v_pos_3179_);
                    v___x_3183_ = 39;
                    v___x_3184_ = lean_uint32_dec_eq(v_curr_3182_, v___x_3183_);
                    if v___x_3184_ == 0 {
                        v___x_3185_ = l_Lake_Toml_isControlChar(v_curr_3182_);
                        if v___x_3185_ == 0 {
                            leanh::lean_inc(v_pos_3179_);
                            v___x_3186_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_3177_,
                                v_c_3176_,
                                v_pos_3179_,
                            );
                            leanh::lean_dec(v_pos_3179_);
                            v_s_3177_ = v___x_3186_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_startPos_3175_);
                            v___x_3188_ = leanh::lean_box(0);
                            v___x_3189_ = l_Lake_Toml_mkUnexpectedCharError(
                                v_s_3177_,
                                v_curr_3182_,
                                v___x_3188_,
                                v___x_3185_,
                            );
                            return v___x_3189_;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3179_);
                        leanh::lean_dec(v_startPos_3175_);
                        v___x_3190_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3177_,
                            v_c_3176_,
                            v_pos_3179_,
                        );
                        leanh::lean_dec(v_pos_3179_);
                        return v___x_3190_;
                    }
                } else {
                    v___x_3191_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0;
                    v___x_3192_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(
                        v_s_3177_,
                        v___x_3191_,
                        v_startPos_3175_,
                    );
                    return v___x_3192_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___boxed(
    mut v_startPos_3193_: *mut leanh::LeanObject,
    mut v_c_3194_: *mut leanh::LeanObject,
    mut v_s_3195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3196_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(
        v_startPos_3193_,
        v_c_3194_,
        v_s_3195_,
    );
    leanh::lean_dec_ref(v_c_3194_);
    return v_res_3196_;
}
pub unsafe fn l_Lake_Toml_literalStringFn(
    mut v_a_3201_: *mut leanh::LeanObject,
    mut v_a_3202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u32 = 0;
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    v_pos_3203_ = leanh::lean_ctor_get(v_a_3202_, 2);
    leanh::lean_inc(v_pos_3203_);
    v___x_3204_ = 39;
    v___x_3205_ = l_Lake_Toml_literalStringFn___closed__1;
    v_s_3206_ = l_Lake_Toml_chFn(v___x_3204_, v___x_3205_, v_a_3201_, v_a_3202_);
    v_errorMsg_3207_ = leanh::lean_ctor_get(v_s_3206_, 4);
    leanh::lean_inc(v_errorMsg_3207_);
    v___x_3208_ = leanh::lean_box(0);
    v___x_3209_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3207_, v___x_3208_);
    if v___x_3209_ == 0 {
        leanh::lean_dec(v_pos_3203_);
        return v_s_3206_;
    } else {
        let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3210_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(
            v_pos_3203_,
            v_a_3201_,
            v_s_3206_,
        );
        return v___x_3210_;
    }
}
pub unsafe fn l_Lake_Toml_literalStringFn___boxed(
    mut v_a_3211_: *mut leanh::LeanObject,
    mut v_a_3212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3213_ = l_Lake_Toml_literalStringFn(v_a_3211_, v_a_3212_);
    leanh::lean_dec_ref(v_a_3211_);
    return v_res_3213_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(
    mut v_startPos_3216_: *mut leanh::LeanObject,
    mut v_quoteDepth_3217_: *mut leanh::LeanObject,
    mut v_c_3218_: *mut leanh::LeanObject,
    mut v_s_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: u8 = 0;
    let mut v_inputString_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u8 = 0;
    let mut v_curr_3225_: u32 = 0;
    let mut v___x_3226_: u32 = 0;
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3230_: u32 = 0;
    let mut v___x_3231_: u8 = 0;
    let mut v___x_3232_: u32 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3220_ = leanh::lean_ctor_get(v_c_3218_, 0);
                v_pos_3221_ = leanh::lean_ctor_get(v_s_3219_, 2);
                v___x_3222_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3220_, v_pos_3221_);
                if v___x_3222_ == 0 {
                    v_inputString_3223_ = leanh::lean_ctor_get(v_toInputContext_3220_, 0);
                    v___x_3224_ = 1;
                    v_curr_3225_ = lean_string_utf8_get_fast(v_inputString_3223_, v_pos_3221_);
                    v___x_3226_ = 39;
                    v___x_3227_ = lean_uint32_dec_eq(v_curr_3225_, v___x_3226_);
                    if v___x_3227_ == 0 {
                        v___x_3228_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3229_ = lean_nat_dec_le(v___x_3228_, v_quoteDepth_3217_);
                        leanh::lean_dec(v_quoteDepth_3217_);
                        if v___x_3229_ == 0 {
                            v___x_3230_ = 10;
                            v___x_3231_ = lean_uint32_dec_eq(v_curr_3225_, v___x_3230_);
                            if v___x_3231_ == 0 {
                                v___x_3232_ = 13;
                                v___x_3233_ = lean_uint32_dec_eq(v_curr_3225_, v___x_3232_);
                                if v___x_3233_ == 0 {
                                    v___x_3234_ = l_Lake_Toml_isControlChar(v_curr_3225_);
                                    if v___x_3234_ == 0 {
                                        leanh::lean_inc(v_pos_3221_);
                                        v___x_3235_ = leanh::lean_unsigned_to_nat(0);
                                        v___x_3236_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                            v_s_3219_,
                                            v_c_3218_,
                                            v_pos_3221_,
                                        );
                                        leanh::lean_dec(v_pos_3221_);
                                        v_quoteDepth_3217_ = v___x_3235_;
                                        v_s_3219_ = v___x_3236_;
                                        state = 0;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_startPos_3216_);
                                        v___x_3238_ = leanh::lean_box(0);
                                        v___x_3239_ = l_Lake_Toml_mkUnexpectedCharError(
                                            v_s_3219_,
                                            v_curr_3225_,
                                            v___x_3238_,
                                            v___x_3224_,
                                        );
                                        return v___x_3239_;
                                    }
                                } else {
                                    leanh::lean_inc(v_pos_3221_);
                                    v___x_3240_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                        v_s_3219_,
                                        v_c_3218_,
                                        v_pos_3221_,
                                    );
                                    leanh::lean_dec(v_pos_3221_);
                                    v_s_3241_ =
                                        l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
                                            v_c_3218_,
                                            v___x_3240_,
                                        );
                                    v_errorMsg_3242_ = leanh::lean_ctor_get(v_s_3241_, 4);
                                    leanh::lean_inc(v_errorMsg_3242_);
                                    v___x_3243_ = leanh::lean_box(0);
                                    v___x_3244_ =
                                        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                            v_errorMsg_3242_,
                                            v___x_3243_,
                                        );
                                    if v___x_3244_ == 0 {
                                        leanh::lean_dec(v_startPos_3216_);
                                        return v_s_3241_;
                                    } else {
                                        v___x_3245_ = leanh::lean_unsigned_to_nat(0);
                                        v_quoteDepth_3217_ = v___x_3245_;
                                        v_s_3219_ = v_s_3241_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_inc(v_pos_3221_);
                                v___x_3247_ = leanh::lean_unsigned_to_nat(0);
                                v___x_3248_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_3219_,
                                    v_c_3218_,
                                    v_pos_3221_,
                                );
                                leanh::lean_dec(v_pos_3221_);
                                v_quoteDepth_3217_ = v___x_3247_;
                                v_s_3219_ = v___x_3248_;
                                state = 0;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_startPos_3216_);
                            return v_s_3219_;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3221_);
                        v_s_3250_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3219_,
                            v_c_3218_,
                            v_pos_3221_,
                        );
                        leanh::lean_dec(v_pos_3221_);
                        v___x_3251_ = leanh::lean_unsigned_to_nat(5);
                        v___x_3252_ = lean_nat_dec_le(v___x_3251_, v_quoteDepth_3217_);
                        if v___x_3252_ == 0 {
                            v___x_3253_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3254_ = lean_nat_add(v_quoteDepth_3217_, v___x_3253_);
                            leanh::lean_dec(v_quoteDepth_3217_);
                            v_quoteDepth_3217_ = v___x_3254_;
                            v_s_3219_ = v_s_3250_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_quoteDepth_3217_);
                            leanh::lean_dec(v_startPos_3216_);
                            v___x_3256_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0;
                            v___x_3257_ = leanh::lean_box(0);
                            v___x_3258_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                                v_s_3250_,
                                v___x_3256_,
                                v___x_3257_,
                                v___x_3224_,
                            );
                            return v___x_3258_;
                        }
                    }
                } else {
                    v___x_3259_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3260_ = lean_nat_dec_le(v___x_3259_, v_quoteDepth_3217_);
                    leanh::lean_dec(v_quoteDepth_3217_);
                    if v___x_3260_ == 0 {
                        v___x_3261_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1;
                        v___x_3262_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(
                            v_s_3219_,
                            v___x_3261_,
                            v_startPos_3216_,
                        );
                        return v___x_3262_;
                    } else {
                        leanh::lean_dec(v_startPos_3216_);
                        return v_s_3219_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(
    mut v_startPos_3263_: *mut leanh::LeanObject,
    mut v_quoteDepth_3264_: *mut leanh::LeanObject,
    mut v_c_3265_: *mut leanh::LeanObject,
    mut v_s_3266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3267_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(
        v_startPos_3263_,
        v_quoteDepth_3264_,
        v_c_3265_,
        v_s_3266_,
    );
    leanh::lean_dec_ref(v_c_3265_);
    return v_res_3267_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(
    mut v_c_3272_: *mut leanh::LeanObject,
    mut v_x_3273_: *mut leanh::LeanObject,
    mut v_x_3274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3276_: u8 = 0;
    let mut v___x_3277_: u32 = 0;
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v_one_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3275_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3276_ = lean_nat_dec_eq(v_x_3273_, v_zero_3275_);
                if v_isZero_3276_ == 1 {
                    leanh::lean_dec(v_x_3273_);
                    return v_x_3274_;
                } else {
                    v___x_3277_ = 39;
                    v___x_3278_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1;
                    v_s_3279_ = l_Lake_Toml_chFn(v___x_3277_, v___x_3278_, v_c_3272_, v_x_3274_);
                    v_errorMsg_3280_ = leanh::lean_ctor_get(v_s_3279_, 4);
                    leanh::lean_inc(v_errorMsg_3280_);
                    v___x_3281_ = leanh::lean_box(0);
                    v___x_3282_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3280_,
                        v___x_3281_,
                    );
                    if v___x_3282_ == 0 {
                        leanh::lean_dec(v_x_3273_);
                        return v_s_3279_;
                    } else {
                        v_one_3283_ = leanh::lean_unsigned_to_nat(1);
                        v_n_3284_ = lean_nat_sub(v_x_3273_, v_one_3283_);
                        leanh::lean_dec(v_x_3273_);
                        v_x_3273_ = v_n_3284_;
                        v_x_3274_ = v_s_3279_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___boxed(
    mut v_c_3286_: *mut leanh::LeanObject,
    mut v_x_3287_: *mut leanh::LeanObject,
    mut v_x_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3289_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v_c_3286_, v_x_3287_, v_x_3288_);
    leanh::lean_dec_ref(v_c_3286_);
    return v_res_3289_;
}
pub unsafe fn l_Lake_Toml_mlLiteralStringFn___lam__0(
    mut v___x_3290_: *mut leanh::LeanObject,
    mut v___y_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3293_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v___y_3291_, v___x_3290_, v___y_3292_);
    return v___x_3293_;
}
pub unsafe fn l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(
    mut v___x_3294_: *mut leanh::LeanObject,
    mut v___y_3295_: *mut leanh::LeanObject,
    mut v___y_3296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3297_ = l_Lake_Toml_mlLiteralStringFn___lam__0(v___x_3294_, v___y_3295_, v___y_3296_);
    leanh::lean_dec_ref(v___y_3295_);
    return v_res_3297_;
}
pub unsafe fn l_Lake_Toml_mlLiteralStringFn(
    mut v_a_3300_: *mut leanh::LeanObject,
    mut v_a_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    v_pos_3302_ = leanh::lean_ctor_get(v_a_3301_, 2);
    leanh::lean_inc(v_pos_3302_);
    v___f_3303_ = l_Lake_Toml_mlLiteralStringFn___closed__0;
    leanh::lean_inc_ref(v_a_3300_);
    v_s_3304_ = l_Lean_Parser_atomicFn(v___f_3303_, v_a_3300_, v_a_3301_);
    v_errorMsg_3305_ = leanh::lean_ctor_get(v_s_3304_, 4);
    leanh::lean_inc(v_errorMsg_3305_);
    v___x_3306_ = leanh::lean_box(0);
    v___x_3307_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3305_, v___x_3306_);
    if v___x_3307_ == 0 {
        leanh::lean_dec(v_pos_3302_);
        leanh::lean_dec_ref(v_a_3300_);
        return v_s_3304_;
    } else {
        let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3308_ = leanh::lean_unsigned_to_nat(0);
        v___x_3309_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(
            v_pos_3302_,
            v___x_3308_,
            v_a_3300_,
            v_s_3304_,
        );
        leanh::lean_dec_ref(v_a_3300_);
        return v___x_3309_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(
    mut v_startPos_3311_: *mut leanh::LeanObject,
    mut v_quoteDepth_3312_: *mut leanh::LeanObject,
    mut v_c_3313_: *mut leanh::LeanObject,
    mut v_s_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: u8 = 0;
    let mut v_inputString_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v_curr_3320_: u32 = 0;
    let mut v___x_3321_: u32 = 0;
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: u32 = 0;
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: u32 = 0;
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: u32 = 0;
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: u8 = 0;
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: u8 = 0;
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u8 = 0;
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3315_ = leanh::lean_ctor_get(v_c_3313_, 0);
                v_pos_3316_ = leanh::lean_ctor_get(v_s_3314_, 2);
                v___x_3317_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3315_, v_pos_3316_);
                if v___x_3317_ == 0 {
                    v_inputString_3318_ = leanh::lean_ctor_get(v_toInputContext_3315_, 0);
                    v___x_3319_ = 1;
                    v_curr_3320_ = lean_string_utf8_get_fast(v_inputString_3318_, v_pos_3316_);
                    v___x_3321_ = 34;
                    v___x_3322_ = lean_uint32_dec_eq(v_curr_3320_, v___x_3321_);
                    if v___x_3322_ == 0 {
                        v___x_3323_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3324_ = lean_nat_dec_le(v___x_3323_, v_quoteDepth_3312_);
                        leanh::lean_dec(v_quoteDepth_3312_);
                        if v___x_3324_ == 0 {
                            v___x_3325_ = 10;
                            v___x_3326_ = lean_uint32_dec_eq(v_curr_3320_, v___x_3325_);
                            if v___x_3326_ == 0 {
                                v___x_3327_ = 13;
                                v___x_3328_ = lean_uint32_dec_eq(v_curr_3320_, v___x_3327_);
                                if v___x_3328_ == 0 {
                                    v___x_3329_ = 92;
                                    v___x_3330_ = lean_uint32_dec_eq(v_curr_3320_, v___x_3329_);
                                    if v___x_3330_ == 0 {
                                        v___x_3331_ = l_Lake_Toml_isControlChar(v_curr_3320_);
                                        if v___x_3331_ == 0 {
                                            leanh::lean_inc(v_pos_3316_);
                                            v___x_3332_ = leanh::lean_unsigned_to_nat(0);
                                            v___x_3333_ =
                                                l_Lean_Parser_ParserState_next_x27___redArg(
                                                    v_s_3314_,
                                                    v_c_3313_,
                                                    v_pos_3316_,
                                                );
                                            leanh::lean_dec(v_pos_3316_);
                                            v_quoteDepth_3312_ = v___x_3332_;
                                            v_s_3314_ = v___x_3333_;
                                            state = 0;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref(v_c_3313_);
                                            leanh::lean_dec(v_startPos_3311_);
                                            v___x_3335_ = leanh::lean_box(0);
                                            v___x_3336_ = l_Lake_Toml_mkUnexpectedCharError(
                                                v_s_3314_,
                                                v_curr_3320_,
                                                v___x_3335_,
                                                v___x_3319_,
                                            );
                                            return v___x_3336_;
                                        }
                                    } else {
                                        leanh::lean_inc(v_pos_3316_);
                                        v___x_3337_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                            v_s_3314_,
                                            v_c_3313_,
                                            v_pos_3316_,
                                        );
                                        leanh::lean_dec(v_pos_3316_);
                                        leanh::lean_inc_ref(v_c_3313_);
                                        v_s_3338_ =
                                            l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(
                                                v___x_3319_,
                                                v_c_3313_,
                                                v___x_3337_,
                                            );
                                        v_errorMsg_3339_ =
                                            leanh::lean_ctor_get(v_s_3338_, 4);
                                        leanh::lean_inc(v_errorMsg_3339_);
                                        v___x_3340_ = leanh::lean_box(0);
                                        v___x_3341_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3339_, v___x_3340_);
                                        if v___x_3341_ == 0 {
                                            leanh::lean_dec_ref(v_c_3313_);
                                            leanh::lean_dec(v_startPos_3311_);
                                            return v_s_3338_;
                                        } else {
                                            v___x_3342_ = leanh::lean_unsigned_to_nat(0);
                                            v_quoteDepth_3312_ = v___x_3342_;
                                            v_s_3314_ = v_s_3338_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_inc(v_pos_3316_);
                                    v___x_3344_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                        v_s_3314_,
                                        v_c_3313_,
                                        v_pos_3316_,
                                    );
                                    leanh::lean_dec(v_pos_3316_);
                                    v_s_3345_ =
                                        l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
                                            v_c_3313_,
                                            v___x_3344_,
                                        );
                                    v_errorMsg_3346_ = leanh::lean_ctor_get(v_s_3345_, 4);
                                    leanh::lean_inc(v_errorMsg_3346_);
                                    v___x_3347_ = leanh::lean_box(0);
                                    v___x_3348_ =
                                        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                            v_errorMsg_3346_,
                                            v___x_3347_,
                                        );
                                    if v___x_3348_ == 0 {
                                        leanh::lean_dec_ref(v_c_3313_);
                                        leanh::lean_dec(v_startPos_3311_);
                                        return v_s_3345_;
                                    } else {
                                        v___x_3349_ = leanh::lean_unsigned_to_nat(0);
                                        v_quoteDepth_3312_ = v___x_3349_;
                                        v_s_3314_ = v_s_3345_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_inc(v_pos_3316_);
                                v___x_3351_ = leanh::lean_unsigned_to_nat(0);
                                v___x_3352_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_3314_,
                                    v_c_3313_,
                                    v_pos_3316_,
                                );
                                leanh::lean_dec(v_pos_3316_);
                                v_quoteDepth_3312_ = v___x_3351_;
                                v_s_3314_ = v___x_3352_;
                                state = 0;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_c_3313_);
                            leanh::lean_dec(v_startPos_3311_);
                            return v_s_3314_;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3316_);
                        v_s_3354_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3314_,
                            v_c_3313_,
                            v_pos_3316_,
                        );
                        leanh::lean_dec(v_pos_3316_);
                        v___x_3355_ = leanh::lean_unsigned_to_nat(5);
                        v___x_3356_ = lean_nat_dec_le(v___x_3355_, v_quoteDepth_3312_);
                        if v___x_3356_ == 0 {
                            v___x_3357_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3358_ = lean_nat_add(v_quoteDepth_3312_, v___x_3357_);
                            leanh::lean_dec(v_quoteDepth_3312_);
                            v_quoteDepth_3312_ = v___x_3358_;
                            v_s_3314_ = v_s_3354_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_c_3313_);
                            leanh::lean_dec(v_quoteDepth_3312_);
                            leanh::lean_dec(v_startPos_3311_);
                            v___x_3360_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0;
                            v___x_3361_ = leanh::lean_box(0);
                            v___x_3362_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                                v_s_3354_,
                                v___x_3360_,
                                v___x_3361_,
                                v___x_3319_,
                            );
                            return v___x_3362_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_c_3313_);
                    v___x_3363_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3364_ = lean_nat_dec_le(v___x_3363_, v_quoteDepth_3312_);
                    leanh::lean_dec(v_quoteDepth_3312_);
                    if v___x_3364_ == 0 {
                        v___x_3365_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0;
                        v___x_3366_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(
                            v_s_3314_,
                            v___x_3365_,
                            v_startPos_3311_,
                        );
                        return v___x_3366_;
                    } else {
                        leanh::lean_dec(v_startPos_3311_);
                        return v_s_3314_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(
    mut v_c_3371_: *mut leanh::LeanObject,
    mut v_x_3372_: *mut leanh::LeanObject,
    mut v_x_3373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3375_: u8 = 0;
    let mut v___x_3376_: u32 = 0;
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: u8 = 0;
    let mut v_one_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3374_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3375_ = lean_nat_dec_eq(v_x_3372_, v_zero_3374_);
                if v_isZero_3375_ == 1 {
                    leanh::lean_dec(v_x_3372_);
                    return v_x_3373_;
                } else {
                    v___x_3376_ = 34;
                    v___x_3377_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1;
                    v_s_3378_ = l_Lake_Toml_chFn(v___x_3376_, v___x_3377_, v_c_3371_, v_x_3373_);
                    v_errorMsg_3379_ = leanh::lean_ctor_get(v_s_3378_, 4);
                    leanh::lean_inc(v_errorMsg_3379_);
                    v___x_3380_ = leanh::lean_box(0);
                    v___x_3381_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3379_,
                        v___x_3380_,
                    );
                    if v___x_3381_ == 0 {
                        leanh::lean_dec(v_x_3372_);
                        return v_s_3378_;
                    } else {
                        v_one_3382_ = leanh::lean_unsigned_to_nat(1);
                        v_n_3383_ = lean_nat_sub(v_x_3372_, v_one_3382_);
                        leanh::lean_dec(v_x_3372_);
                        v_x_3372_ = v_n_3383_;
                        v_x_3373_ = v_s_3378_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___boxed(
    mut v_c_3385_: *mut leanh::LeanObject,
    mut v_x_3386_: *mut leanh::LeanObject,
    mut v_x_3387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v_c_3385_, v_x_3386_, v_x_3387_);
    leanh::lean_dec_ref(v_c_3385_);
    return v_res_3388_;
}
pub unsafe fn l_Lake_Toml_mlBasicStringFn___lam__0(
    mut v___x_3389_: *mut leanh::LeanObject,
    mut v___y_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3392_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v___y_3390_, v___x_3389_, v___y_3391_);
    return v___x_3392_;
}
pub unsafe fn l_Lake_Toml_mlBasicStringFn___lam__0___boxed(
    mut v___x_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3396_ = l_Lake_Toml_mlBasicStringFn___lam__0(v___x_3393_, v___y_3394_, v___y_3395_);
    leanh::lean_dec_ref(v___y_3394_);
    return v_res_3396_;
}
pub unsafe fn l_Lake_Toml_mlBasicStringFn(
    mut v_a_3399_: *mut leanh::LeanObject,
    mut v_a_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: u8 = 0;
    v_pos_3401_ = leanh::lean_ctor_get(v_a_3400_, 2);
    leanh::lean_inc(v_pos_3401_);
    v___f_3402_ = l_Lake_Toml_mlBasicStringFn___closed__0;
    leanh::lean_inc_ref(v_a_3399_);
    v_s_3403_ = l_Lean_Parser_atomicFn(v___f_3402_, v_a_3399_, v_a_3400_);
    v_errorMsg_3404_ = leanh::lean_ctor_get(v_s_3403_, 4);
    leanh::lean_inc(v_errorMsg_3404_);
    v___x_3405_ = leanh::lean_box(0);
    v___x_3406_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3404_, v___x_3405_);
    if v___x_3406_ == 0 {
        leanh::lean_dec(v_pos_3401_);
        leanh::lean_dec_ref(v_a_3399_);
        return v_s_3403_;
    } else {
        let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3407_ = leanh::lean_unsigned_to_nat(0);
        v___x_3408_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(
            v_pos_3401_,
            v___x_3407_,
            v_a_3399_,
            v_s_3403_,
        );
        return v___x_3408_;
    }
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3415_: u32 = 0;
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ = 58;
    v___x_3416_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_3417_ = lean_string_push(v___x_3416_, v___x_3415_);
    return v___x_3417_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4,
    );
    v___x_3419_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_3420_ = lean_string_append(v___x_3419_, v___x_3418_);
    return v___x_3420_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_3422_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5,
    );
    v___x_3423_ = lean_string_append(v___x_3422_, v___x_3421_);
    return v___x_3423_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = leanh::lean_box(0);
    v___x_3425_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6,
    );
    v___x_3426_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3426_, 0, v___x_3425_);
    leanh::lean_ctor_set(v___x_3426_, 1, v___x_3424_);
    return v___x_3426_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(
    mut v_a_3431_: *mut leanh::LeanObject,
    mut v_a_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    v___x_3433_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1;
    v_s_3434_ = l_Lake_Toml_digitPairFn(v___x_3433_, v_a_3431_, v_a_3432_);
    v_errorMsg_3435_ = leanh::lean_ctor_get(v_s_3434_, 4);
    leanh::lean_inc(v_errorMsg_3435_);
    v___x_3436_ = leanh::lean_box(0);
    v___x_3437_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3435_, v___x_3436_);
    if v___x_3437_ == 0 {
        return v_s_3434_;
    } else {
        let mut v___x_3438_: u32 = 0;
        let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3442_: u8 = 0;
        v___x_3438_ = 58;
        v___x_3439_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7,
        );
        v_s_3440_ = l_Lake_Toml_chFn(v___x_3438_, v___x_3439_, v_a_3431_, v_s_3434_);
        v_errorMsg_3441_ = leanh::lean_ctor_get(v_s_3440_, 4);
        leanh::lean_inc(v_errorMsg_3441_);
        v___x_3442_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3441_,
            v___x_3436_,
        );
        if v___x_3442_ == 0 {
            return v_s_3440_;
        } else {
            let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3443_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9;
            v___x_3444_ = l_Lake_Toml_digitPairFn(v___x_3443_, v_a_3431_, v_s_3440_);
            return v___x_3444_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(
    mut v_a_3445_: *mut leanh::LeanObject,
    mut v_a_3446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3447_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_a_3445_, v_a_3446_);
    leanh::lean_dec_ref(v_a_3445_);
    return v_res_3447_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(
    mut v_allowOffset_3449_: u8,
    mut v_curr_3450_: u32,
    mut v_nextPos_3451_: *mut leanh::LeanObject,
    mut v_c_3452_: *mut leanh::LeanObject,
    mut v_s_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3455_: u8 = 0;
    let mut v___y_3456_: u8 = 0;
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3463_: u8 = 0;
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: u32 = 0;
    let mut v___x_3466_: u8 = 0;
    let mut v___x_3467_: u32 = 0;
    let mut v___x_3468_: u8 = 0;
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: u32 = 0;
    let mut v___x_3474_: u8 = 0;
    let mut v___x_3475_: u32 = 0;
    let mut v___x_3476_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3473_ = 90;
                v___x_3474_ = lean_uint32_dec_eq(v_curr_3450_, v___x_3473_);
                if v___x_3474_ == 0 {
                    v___x_3475_ = 122;
                    v___x_3476_ = lean_uint32_dec_eq(v_curr_3450_, v___x_3475_);
                    v___y_3463_ = v___x_3476_;
                    state = 2;
                    continue;
                } else {
                    v___y_3463_ = v___x_3474_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_3456_ == 0 {
                    leanh::lean_dec(v_nextPos_3451_);
                    return v_s_3453_;
                } else {
                    if v_allowOffset_3449_ == 0 {
                        leanh::lean_dec(v_nextPos_3451_);
                        v___x_3457_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
                        v___x_3458_ = leanh::lean_box(0);
                        v___x_3459_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                            v_s_3453_,
                            v___x_3457_,
                            v___x_3458_,
                            v___y_3455_,
                        );
                        return v___x_3459_;
                    } else {
                        v___x_3460_ = l_Lean_Parser_ParserState_setPos(v_s_3453_, v_nextPos_3451_);
                        v___x_3461_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(
                            v_c_3452_,
                            v___x_3460_,
                        );
                        return v___x_3461_;
                    }
                }
            }
            2 => {
                v___x_3464_ = 1;
                if v___y_3463_ == 0 {
                    v___x_3465_ = 43;
                    v___x_3466_ = lean_uint32_dec_eq(v_curr_3450_, v___x_3465_);
                    if v___x_3466_ == 0 {
                        v___x_3467_ = 45;
                        v___x_3468_ = lean_uint32_dec_eq(v_curr_3450_, v___x_3467_);
                        v___y_3455_ = v___x_3464_;
                        v___y_3456_ = v___x_3468_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3455_ = v___x_3464_;
                        v___y_3456_ = v___x_3466_;
                        state = 1;
                        continue;
                    }
                } else {
                    if v_allowOffset_3449_ == 0 {
                        leanh::lean_dec(v_nextPos_3451_);
                        v___x_3469_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
                        v___x_3470_ = leanh::lean_box(0);
                        v___x_3471_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                            v_s_3453_,
                            v___x_3469_,
                            v___x_3470_,
                            v___x_3464_,
                        );
                        return v___x_3471_;
                    } else {
                        v___x_3472_ = l_Lean_Parser_ParserState_setPos(v_s_3453_, v_nextPos_3451_);
                        return v___x_3472_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(
    mut v_allowOffset_3477_: *mut leanh::LeanObject,
    mut v_curr_3478_: *mut leanh::LeanObject,
    mut v_nextPos_3479_: *mut leanh::LeanObject,
    mut v_c_3480_: *mut leanh::LeanObject,
    mut v_s_3481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowOffset_boxed_3482_: u8 = 0;
    let mut v_curr_boxed_3483_: u32 = 0;
    let mut v_res_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowOffset_boxed_3482_ = (leanh::lean_unbox(v_allowOffset_3477_) as u8);
    v_curr_boxed_3483_ = leanh::lean_unbox_uint32(v_curr_3478_);
    leanh::lean_dec(v_curr_3478_);
    v_res_3484_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(
        v_allowOffset_boxed_3482_,
        v_curr_boxed_3483_,
        v_nextPos_3479_,
        v_c_3480_,
        v_s_3481_,
    );
    leanh::lean_dec_ref(v_c_3480_);
    return v_res_3484_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(
    mut v_x_3485_: u32,
) -> u8 {
    let mut v___x_3486_: u32 = 0;
    let mut v___x_3487_: u8 = 0;
    v___x_3486_ = 48;
    v___x_3487_ = lean_uint32_dec_le(v___x_3486_, v_x_3485_);
    if v___x_3487_ == 0 {
        return v___x_3487_;
    } else {
        let mut v___x_3488_: u32 = 0;
        let mut v___x_3489_: u8 = 0;
        v___x_3488_ = 57;
        v___x_3489_ = lean_uint32_dec_le(v_x_3485_, v___x_3488_);
        return v___x_3489_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(
    mut v_x_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_512__boxed_3491_: u32 = 0;
    let mut v_res_3492_: u8 = 0;
    let mut v_r_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_512__boxed_3491_ = leanh::lean_unbox_uint32(v_x_3490_);
    leanh::lean_dec(v_x_3490_);
    v_res_3492_ =
        l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(v_x_512__boxed_3491_);
    v_r_3493_ = leanh::lean_box((v_res_3492_) as usize);
    return v_r_3493_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(
    mut v_allowOffset_3499_: u8,
    mut v_c_3500_: *mut leanh::LeanObject,
    mut v_s_3501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut v_inputString_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3506_: u32 = 0;
    let mut v___x_3507_: u32 = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3511_: u8 = 0;
    let mut v___y_3512_: u8 = 0;
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3519_: u8 = 0;
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: u32 = 0;
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: u32 = 0;
    let mut v___x_3524_: u8 = 0;
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u32 = 0;
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: u32 = 0;
    let mut v___x_3532_: u8 = 0;
    let mut v___f_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: u32 = 0;
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3546_: u8 = 0;
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3552_: u8 = 0;
    let mut v___x_3553_: u32 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: u32 = 0;
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: u32 = 0;
    let mut v___x_3561_: u8 = 0;
    let mut v___x_3562_: u32 = 0;
    let mut v___x_3563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3502_ = leanh::lean_ctor_get(v_c_3500_, 0);
                v_pos_3503_ = leanh::lean_ctor_get(v_s_3501_, 2);
                v___x_3504_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3502_, v_pos_3503_);
                if v___x_3504_ == 0 {
                    v_inputString_3505_ = leanh::lean_ctor_get(v_toInputContext_3502_, 0);
                    v_curr_3506_ = lean_string_utf8_get_fast(v_inputString_3505_, v_pos_3503_);
                    v___x_3507_ = 46;
                    v___x_3508_ = lean_uint32_dec_eq(v_curr_3506_, v___x_3507_);
                    if v___x_3508_ == 0 {
                        v___x_3509_ = lean_string_utf8_next_fast(v_inputString_3505_, v_pos_3503_);
                        v___x_3529_ = 90;
                        v___x_3530_ = lean_uint32_dec_eq(v_curr_3506_, v___x_3529_);
                        if v___x_3530_ == 0 {
                            v___x_3531_ = 122;
                            v___x_3532_ = lean_uint32_dec_eq(v_curr_3506_, v___x_3531_);
                            v___y_3519_ = v___x_3532_;
                            state = 2;
                            continue;
                        } else {
                            v___y_3519_ = v___x_3530_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3503_);
                        v___f_3533_ =
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0;
                        v_s_3534_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3501_,
                            v_c_3500_,
                            v_pos_3503_,
                        );
                        leanh::lean_dec(v_pos_3503_);
                        v___x_3535_ = leanh::lean_box(0);
                        v___x_3536_ =
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2;
                        v_s_3537_ = l_Lake_Toml_takeWhile1Fn(
                            v___f_3533_,
                            v___x_3536_,
                            v_c_3500_,
                            v_s_3534_,
                        );
                        v_pos_3538_ = leanh::lean_ctor_get(v_s_3537_, 2);
                        leanh::lean_inc(v_pos_3538_);
                        v_errorMsg_3539_ = leanh::lean_ctor_get(v_s_3537_, 4);
                        leanh::lean_inc(v_errorMsg_3539_);
                        v___x_3540_ = leanh::lean_box(0);
                        v___x_3541_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                            v_errorMsg_3539_,
                            v___x_3540_,
                        );
                        if v___x_3541_ == 0 {
                            leanh::lean_dec(v_pos_3538_);
                            return v_s_3537_;
                        } else {
                            if v___x_3504_ == 0 {
                                v___x_3542_ = l_Lean_Parser_InputContext_atEnd(
                                    v_toInputContext_3502_,
                                    v_pos_3538_,
                                );
                                if v___x_3542_ == 0 {
                                    v___x_3543_ =
                                        lean_string_utf8_get_fast(v_inputString_3505_, v_pos_3538_);
                                    v___x_3544_ = lean_string_utf8_next_fast(
                                        v_inputString_3505_,
                                        v_pos_3538_,
                                    );
                                    leanh::lean_dec(v_pos_3538_);
                                    v___x_3560_ = 90;
                                    v___x_3561_ = lean_uint32_dec_eq(v___x_3543_, v___x_3560_);
                                    if v___x_3561_ == 0 {
                                        v___x_3562_ = 122;
                                        v___x_3563_ = lean_uint32_dec_eq(v___x_3543_, v___x_3562_);
                                        v___y_3552_ = v___x_3563_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v___y_3552_ = v___x_3561_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_pos_3538_);
                                    return v_s_3537_;
                                }
                            } else {
                                leanh::lean_dec(v_pos_3538_);
                                return v_s_3537_;
                            }
                        }
                    }
                } else {
                    return v_s_3501_;
                }
            }
            1 => {
                if v___y_3512_ == 0 {
                    return v_s_3501_;
                } else {
                    if v_allowOffset_3499_ == 0 {
                        v___x_3513_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
                        v___x_3514_ = leanh::lean_box(0);
                        v___x_3515_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                            v_s_3501_,
                            v___x_3513_,
                            v___x_3514_,
                            v___y_3511_,
                        );
                        return v___x_3515_;
                    } else {
                        v___x_3516_ = l_Lean_Parser_ParserState_setPos(v_s_3501_, v___x_3509_);
                        v___x_3517_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(
                            v_c_3500_,
                            v___x_3516_,
                        );
                        return v___x_3517_;
                    }
                }
            }
            2 => {
                v___x_3520_ = 1;
                if v___y_3519_ == 0 {
                    v___x_3521_ = 43;
                    v___x_3522_ = lean_uint32_dec_eq(v_curr_3506_, v___x_3521_);
                    if v___x_3522_ == 0 {
                        v___x_3523_ = 45;
                        v___x_3524_ = lean_uint32_dec_eq(v_curr_3506_, v___x_3523_);
                        v___y_3511_ = v___x_3520_;
                        v___y_3512_ = v___x_3524_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3511_ = v___x_3520_;
                        v___y_3512_ = v___x_3522_;
                        state = 1;
                        continue;
                    }
                } else {
                    if v_allowOffset_3499_ == 0 {
                        v___x_3525_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
                        v___x_3526_ = leanh::lean_box(0);
                        v___x_3527_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                            v_s_3501_,
                            v___x_3525_,
                            v___x_3526_,
                            v___x_3520_,
                        );
                        return v___x_3527_;
                    } else {
                        v___x_3528_ = l_Lean_Parser_ParserState_setPos(v_s_3501_, v___x_3509_);
                        return v___x_3528_;
                    }
                }
            }
            3 => {
                if v___y_3546_ == 0 {
                    return v_s_3537_;
                } else {
                    if v_allowOffset_3499_ == 0 {
                        v___x_3547_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
                        v___x_3548_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                            v_s_3537_,
                            v___x_3547_,
                            v___x_3535_,
                            v___x_3541_,
                        );
                        return v___x_3548_;
                    } else {
                        v___x_3549_ = l_Lean_Parser_ParserState_setPos(v_s_3537_, v___x_3544_);
                        v___x_3550_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(
                            v_c_3500_,
                            v___x_3549_,
                        );
                        return v___x_3550_;
                    }
                }
            }
            4 => {
                if v___y_3552_ == 0 {
                    v___x_3553_ = 43;
                    v___x_3554_ = lean_uint32_dec_eq(v___x_3543_, v___x_3553_);
                    if v___x_3554_ == 0 {
                        v___x_3555_ = 45;
                        v___x_3556_ = lean_uint32_dec_eq(v___x_3543_, v___x_3555_);
                        v___y_3546_ = v___x_3556_;
                        state = 3;
                        continue;
                    } else {
                        v___y_3546_ = v___x_3554_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_allowOffset_3499_ == 0 {
                        v___x_3557_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
                        v___x_3558_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                            v_s_3537_,
                            v___x_3557_,
                            v___x_3535_,
                            v___x_3541_,
                        );
                        return v___x_3558_;
                    } else {
                        v___x_3559_ = l_Lean_Parser_ParserState_setPos(v_s_3537_, v___x_3544_);
                        return v___x_3559_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(
    mut v_allowOffset_3564_: *mut leanh::LeanObject,
    mut v_c_3565_: *mut leanh::LeanObject,
    mut v_s_3566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowOffset_boxed_3567_: u8 = 0;
    let mut v_res_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowOffset_boxed_3567_ = (leanh::lean_unbox(v_allowOffset_3564_) as u8);
    v_res_3568_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(
        v_allowOffset_boxed_3567_,
        v_c_3565_,
        v_s_3566_,
    );
    leanh::lean_dec_ref(v_c_3565_);
    return v_res_3568_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(
    mut v_allowOffset_3573_: u8,
    mut v_a_3574_: *mut leanh::LeanObject,
    mut v_a_3575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: u8 = 0;
    v___x_3576_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9;
    v_s_3577_ = l_Lake_Toml_digitPairFn(v___x_3576_, v_a_3574_, v_a_3575_);
    v_errorMsg_3578_ = leanh::lean_ctor_get(v_s_3577_, 4);
    leanh::lean_inc(v_errorMsg_3578_);
    v___x_3579_ = leanh::lean_box(0);
    v___x_3580_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3578_, v___x_3579_);
    if v___x_3580_ == 0 {
        return v_s_3577_;
    } else {
        let mut v___x_3581_: u32 = 0;
        let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3585_: u8 = 0;
        v___x_3581_ = 58;
        v___x_3582_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7,
        );
        v_s_3583_ = l_Lake_Toml_chFn(v___x_3581_, v___x_3582_, v_a_3574_, v_s_3577_);
        v_errorMsg_3584_ = leanh::lean_ctor_get(v_s_3583_, 4);
        leanh::lean_inc(v_errorMsg_3584_);
        v___x_3585_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3584_,
            v___x_3579_,
        );
        if v___x_3585_ == 0 {
            return v_s_3583_;
        } else {
            let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_errorMsg_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3589_: u8 = 0;
            v___x_3586_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1;
            v_s_3587_ = l_Lake_Toml_digitPairFn(v___x_3586_, v_a_3574_, v_s_3583_);
            v_errorMsg_3588_ = leanh::lean_ctor_get(v_s_3587_, 4);
            leanh::lean_inc(v_errorMsg_3588_);
            v___x_3589_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                v_errorMsg_3588_,
                v___x_3579_,
            );
            if v___x_3589_ == 0 {
                return v_s_3587_;
            } else {
                let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3590_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(
                    v_allowOffset_3573_,
                    v_a_3574_,
                    v_s_3587_,
                );
                return v___x_3590_;
            }
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(
    mut v_allowOffset_3591_: *mut leanh::LeanObject,
    mut v_a_3592_: *mut leanh::LeanObject,
    mut v_a_3593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowOffset_boxed_3594_: u8 = 0;
    let mut v_res_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowOffset_boxed_3594_ = (leanh::lean_unbox(v_allowOffset_3591_) as u8);
    v_res_3595_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(
        v_allowOffset_boxed_3594_,
        v_a_3592_,
        v_a_3593_,
    );
    leanh::lean_dec_ref(v_a_3592_);
    return v_res_3595_;
}
pub unsafe fn l_Lake_Toml_timeFn(
    mut v_allowOffset_3600_: u8,
    mut v_a_3601_: *mut leanh::LeanObject,
    mut v_a_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    v___x_3603_ = l_Lake_Toml_timeFn___closed__1;
    v_s_3604_ = l_Lake_Toml_digitPairFn(v___x_3603_, v_a_3601_, v_a_3602_);
    v_errorMsg_3605_ = leanh::lean_ctor_get(v_s_3604_, 4);
    leanh::lean_inc(v_errorMsg_3605_);
    v___x_3606_ = leanh::lean_box(0);
    v___x_3607_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3605_, v___x_3606_);
    if v___x_3607_ == 0 {
        return v_s_3604_;
    } else {
        let mut v___x_3608_: u32 = 0;
        let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3612_: u8 = 0;
        v___x_3608_ = 58;
        v___x_3609_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7,
        );
        v_s_3610_ = l_Lake_Toml_chFn(v___x_3608_, v___x_3609_, v_a_3601_, v_s_3604_);
        v_errorMsg_3611_ = leanh::lean_ctor_get(v_s_3610_, 4);
        leanh::lean_inc(v_errorMsg_3611_);
        v___x_3612_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3611_,
            v___x_3606_,
        );
        if v___x_3612_ == 0 {
            return v_s_3610_;
        } else {
            let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3613_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(
                v_allowOffset_3600_,
                v_a_3601_,
                v_s_3610_,
            );
            return v___x_3613_;
        }
    }
}
pub unsafe fn l_Lake_Toml_timeFn___boxed(
    mut v_allowOffset_3614_: *mut leanh::LeanObject,
    mut v_a_3615_: *mut leanh::LeanObject,
    mut v_a_3616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowOffset_boxed_3617_: u8 = 0;
    let mut v_res_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowOffset_boxed_3617_ = (leanh::lean_unbox(v_allowOffset_3614_) as u8);
    v_res_3618_ = l_Lake_Toml_timeFn(v_allowOffset_boxed_3617_, v_a_3615_, v_a_3616_);
    leanh::lean_dec_ref(v_a_3615_);
    return v_res_3618_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(
    mut v_c_3619_: *mut leanh::LeanObject,
    mut v_s_3620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v_inputString_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3629_: u32 = 0;
    let mut v___x_3630_: u32 = 0;
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3632_: u32 = 0;
    let mut v___x_3633_: u8 = 0;
    let mut v___x_3634_: u32 = 0;
    let mut v___x_3635_: u8 = 0;
    let mut v_tPos_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_3621_ = leanh::lean_ctor_get(v_s_3620_, 2);
                v_toInputContext_3622_ = leanh::lean_ctor_get(v_c_3619_, 0);
                v___x_3623_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3622_, v_pos_3621_);
                if v___x_3623_ == 0 {
                    v_inputString_3624_ = leanh::lean_ctor_get(v_toInputContext_3622_, 0);
                    v___x_3625_ = 1;
                    v_curr_3629_ = lean_string_utf8_get_fast(v_inputString_3624_, v_pos_3621_);
                    v___x_3630_ = 84;
                    v___x_3631_ = lean_uint32_dec_eq(v_curr_3629_, v___x_3630_);
                    if v___x_3631_ == 0 {
                        v___x_3632_ = 116;
                        v___x_3633_ = lean_uint32_dec_eq(v_curr_3629_, v___x_3632_);
                        if v___x_3633_ == 0 {
                            v___x_3634_ = 32;
                            v___x_3635_ = lean_uint32_dec_eq(v_curr_3629_, v___x_3634_);
                            if v___x_3635_ == 0 {
                                return v_s_3620_;
                            } else {
                                leanh::lean_inc(v_pos_3621_);
                                v_tPos_3636_ =
                                    lean_string_utf8_next_fast(v_inputString_3624_, v_pos_3621_);
                                v___x_3637_ =
                                    l_Lean_Parser_ParserState_setPos(v_s_3620_, v_tPos_3636_);
                                v_s_3638_ = l_Lake_Toml_timeFn(v___x_3625_, v_c_3619_, v___x_3637_);
                                v_errorMsg_3646_ = leanh::lean_ctor_get(v_s_3638_, 4);
                                leanh::lean_inc(v_errorMsg_3646_);
                                v___x_3647_ = leanh::lean_box(0);
                                v___x_3648_ =
                                    l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                        v_errorMsg_3646_,
                                        v___x_3647_,
                                    );
                                if v___x_3648_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    if v___x_3633_ == 0 {
                                        leanh::lean_dec(v_pos_3621_);
                                        return v_s_3638_;
                                    } else {
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_inc(v_pos_3621_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3621_);
                        state = 1;
                        continue;
                    }
                } else {
                    return v_s_3620_;
                }
            }
            1 => {
                v___x_3627_ =
                    l_Lean_Parser_ParserState_next_x27___redArg(v_s_3620_, v_c_3619_, v_pos_3621_);
                leanh::lean_dec(v_pos_3621_);
                v___x_3628_ = l_Lake_Toml_timeFn(v___x_3625_, v_c_3619_, v___x_3627_);
                return v___x_3628_;
            }
            2 => {
                v_pos_3640_ = leanh::lean_ctor_get(v_s_3638_, 2);
                leanh::lean_inc(v_pos_3640_);
                v___x_3641_ = lean_nat_dec_eq(v_pos_3640_, v_tPos_3636_);
                leanh::lean_dec(v_pos_3640_);
                if v___x_3641_ == 0 {
                    leanh::lean_dec(v_pos_3621_);
                    return v_s_3638_;
                } else {
                    v___x_3642_ = l_Lean_Parser_ParserState_stackSize(v_s_3638_);
                    v___x_3643_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3644_ = lean_nat_sub(v___x_3642_, v___x_3643_);
                    leanh::lean_dec(v___x_3642_);
                    v___x_3645_ =
                        l_Lean_Parser_ParserState_restore(v_s_3638_, v___x_3644_, v_pos_3621_);
                    leanh::lean_dec(v___x_3644_);
                    return v___x_3645_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(
    mut v_c_3649_: *mut leanh::LeanObject,
    mut v_s_3650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3651_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_c_3649_, v_s_3650_);
    leanh::lean_dec_ref(v_c_3649_);
    return v_res_3651_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3656_: u32 = 0;
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3656_ = 45;
    v___x_3657_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_3658_ = lean_string_push(v___x_3657_, v___x_3656_);
    return v___x_3658_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2,
    );
    v___x_3660_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_3661_ = lean_string_append(v___x_3660_, v___x_3659_);
    return v___x_3661_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3662_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_3663_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3,
    );
    v___x_3664_ = lean_string_append(v___x_3663_, v___x_3662_);
    return v___x_3664_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = leanh::lean_box(0);
    v___x_3666_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4,
    );
    v___x_3667_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    leanh::lean_ctor_set(v___x_3667_, 1, v___x_3665_);
    return v___x_3667_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(
    mut v_a_3672_: *mut leanh::LeanObject,
    mut v_a_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    v___x_3674_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1;
    v_s_3675_ = l_Lake_Toml_digitPairFn(v___x_3674_, v_a_3672_, v_a_3673_);
    v_errorMsg_3676_ = leanh::lean_ctor_get(v_s_3675_, 4);
    leanh::lean_inc(v_errorMsg_3676_);
    v___x_3677_ = leanh::lean_box(0);
    v___x_3678_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3676_, v___x_3677_);
    if v___x_3678_ == 0 {
        return v_s_3675_;
    } else {
        let mut v___x_3679_: u32 = 0;
        let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3683_: u8 = 0;
        v___x_3679_ = 45;
        v___x_3680_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5,
        );
        v_s_3681_ = l_Lake_Toml_chFn(v___x_3679_, v___x_3680_, v_a_3672_, v_s_3675_);
        v_errorMsg_3682_ = leanh::lean_ctor_get(v_s_3681_, 4);
        leanh::lean_inc(v_errorMsg_3682_);
        v___x_3683_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3682_,
            v___x_3677_,
        );
        if v___x_3683_ == 0 {
            return v_s_3681_;
        } else {
            let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_errorMsg_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3687_: u8 = 0;
            v___x_3684_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7;
            v_s_3685_ = l_Lake_Toml_digitPairFn(v___x_3684_, v_a_3672_, v_s_3681_);
            v_errorMsg_3686_ = leanh::lean_ctor_get(v_s_3685_, 4);
            leanh::lean_inc(v_errorMsg_3686_);
            v___x_3687_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                v_errorMsg_3686_,
                v___x_3677_,
            );
            if v___x_3687_ == 0 {
                return v_s_3685_;
            } else {
                let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3688_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_a_3672_, v_s_3685_);
                return v___x_3688_;
            }
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(
    mut v_a_3689_: *mut leanh::LeanObject,
    mut v_a_3690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3691_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_3689_, v_a_3690_);
    leanh::lean_dec_ref(v_a_3689_);
    return v_res_3691_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(
    mut v_c_3696_: *mut leanh::LeanObject,
    mut v_x_3697_: *mut leanh::LeanObject,
    mut v_x_3698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3700_: u8 = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: u8 = 0;
    let mut v_one_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3699_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3700_ = lean_nat_dec_eq(v_x_3697_, v_zero_3699_);
                if v_isZero_3700_ == 1 {
                    leanh::lean_dec(v_x_3697_);
                    return v_x_3698_;
                } else {
                    v___x_3701_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1;
                    v_s_3702_ = l_Lake_Toml_digitFn(v___x_3701_, v_c_3696_, v_x_3698_);
                    v_errorMsg_3703_ = leanh::lean_ctor_get(v_s_3702_, 4);
                    leanh::lean_inc(v_errorMsg_3703_);
                    v___x_3704_ = leanh::lean_box(0);
                    v___x_3705_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3703_,
                        v___x_3704_,
                    );
                    if v___x_3705_ == 0 {
                        leanh::lean_dec(v_x_3697_);
                        return v_s_3702_;
                    } else {
                        v_one_3706_ = leanh::lean_unsigned_to_nat(1);
                        v_n_3707_ = lean_nat_sub(v_x_3697_, v_one_3706_);
                        leanh::lean_dec(v_x_3697_);
                        v_x_3697_ = v_n_3707_;
                        v_x_3698_ = v_s_3702_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___boxed(
    mut v_c_3709_: *mut leanh::LeanObject,
    mut v_x_3710_: *mut leanh::LeanObject,
    mut v_x_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3712_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_c_3709_, v_x_3710_, v_x_3711_);
    leanh::lean_dec_ref(v_c_3709_);
    return v_res_3712_;
}
pub unsafe fn l_Lake_Toml_dateTimeFn(
    mut v_a_3713_: *mut leanh::LeanObject,
    mut v_a_3714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: u8 = 0;
    v___x_3715_ = leanh::lean_unsigned_to_nat(4);
    v_s_3716_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_a_3713_, v___x_3715_, v_a_3714_);
    v_errorMsg_3717_ = leanh::lean_ctor_get(v_s_3716_, 4);
    leanh::lean_inc(v_errorMsg_3717_);
    v___x_3718_ = leanh::lean_box(0);
    v___x_3719_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3717_, v___x_3718_);
    if v___x_3719_ == 0 {
        return v_s_3716_;
    } else {
        let mut v___x_3720_: u32 = 0;
        let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3724_: u8 = 0;
        v___x_3720_ = 45;
        v___x_3721_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5,
        );
        v_s_3722_ = l_Lake_Toml_chFn(v___x_3720_, v___x_3721_, v_a_3713_, v_s_3716_);
        v_errorMsg_3723_ = leanh::lean_ctor_get(v_s_3722_, 4);
        leanh::lean_inc(v_errorMsg_3723_);
        v___x_3724_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3723_,
            v___x_3718_,
        );
        if v___x_3724_ == 0 {
            return v_s_3722_;
        } else {
            let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3725_ =
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_3713_, v_s_3722_);
            return v___x_3725_;
        }
    }
}
pub unsafe fn l_Lake_Toml_dateTimeFn___boxed(
    mut v_a_3726_: *mut leanh::LeanObject,
    mut v_a_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3728_ = l_Lake_Toml_dateTimeFn(v_a_3726_, v_a_3727_);
    leanh::lean_dec_ref(v_a_3726_);
    return v_res_3728_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(
    mut v_c_3733_: *mut leanh::LeanObject,
    mut v_s_3734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v_inputString_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: u32 = 0;
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3745_: u32 = 0;
    let mut v___x_3746_: u32 = 0;
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: u32 = 0;
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: u8 = 0;
    let mut v___y_3752_: u8 = 0;
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: u32 = 0;
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: u32 = 0;
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: u32 = 0;
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3735_ = leanh::lean_ctor_get(v_c_3733_, 0);
                v_pos_3736_ = leanh::lean_ctor_get(v_s_3734_, 2);
                v_expected_3737_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1;
                v___x_3738_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3735_, v_pos_3736_);
                if v___x_3738_ == 0 {
                    v_inputString_3739_ = leanh::lean_ctor_get(v_toInputContext_3735_, 0);
                    v___f_3740_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0;
                    v_curr_3745_ = lean_string_utf8_get_fast(v_inputString_3739_, v_pos_3736_);
                    v___x_3746_ = 45;
                    v___x_3747_ = lean_uint32_dec_eq(v_curr_3745_, v___x_3746_);
                    if v___x_3747_ == 0 {
                        v___x_3748_ = 43;
                        v___x_3749_ = lean_uint32_dec_eq(v_curr_3745_, v___x_3748_);
                        if v___x_3749_ == 0 {
                            v___x_3750_ = 1;
                            v___x_3757_ = 48;
                            v___x_3758_ = lean_uint32_dec_le(v___x_3757_, v_curr_3745_);
                            if v___x_3758_ == 0 {
                                v___y_3752_ = v___x_3758_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3759_ = 57;
                                v___x_3760_ = lean_uint32_dec_le(v_curr_3745_, v___x_3759_);
                                v___y_3752_ = v___x_3760_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_inc(v_pos_3736_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3736_);
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3761_ = l_Lean_Parser_ParserState_mkEOIError(v_s_3734_, v_expected_3737_);
                    return v___x_3761_;
                }
            }
            1 => {
                v_s_3742_ =
                    l_Lean_Parser_ParserState_next_x27___redArg(v_s_3734_, v_c_3733_, v_pos_3736_);
                leanh::lean_dec(v_pos_3736_);
                v___x_3743_ = 95;
                v___x_3744_ = l_Lake_Toml_sepByChar1Fn(
                    v___f_3740_,
                    v___x_3743_,
                    v_expected_3737_,
                    v_c_3733_,
                    v_s_3742_,
                );
                return v___x_3744_;
            }
            2 => {
                if v___y_3752_ == 0 {
                    v___x_3753_ = l_Lake_Toml_mkUnexpectedCharError(
                        v_s_3734_,
                        v_curr_3745_,
                        v_expected_3737_,
                        v___x_3750_,
                    );
                    return v___x_3753_;
                } else {
                    leanh::lean_inc(v_pos_3736_);
                    v_s_3754_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3734_,
                        v_c_3733_,
                        v_pos_3736_,
                    );
                    leanh::lean_dec(v_pos_3736_);
                    v___x_3755_ = 95;
                    v___x_3756_ = l_Lake_Toml_sepByChar1AuxFn(
                        v___f_3740_,
                        v___x_3755_,
                        v_expected_3737_,
                        v_c_3733_,
                        v_s_3754_,
                    );
                    return v___x_3756_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(
    mut v_c_3762_: *mut leanh::LeanObject,
    mut v_s_3763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3764_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_3762_, v_s_3763_);
    leanh::lean_dec_ref(v_c_3762_);
    return v_res_3764_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(
    mut v_c_3765_: *mut leanh::LeanObject,
    mut v_s_3766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: u8 = 0;
    let mut v_inputString_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3774_: u32 = 0;
    let mut v___x_3775_: u32 = 0;
    let mut v___x_3776_: u8 = 0;
    let mut v___x_3777_: u32 = 0;
    let mut v___x_3778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3767_ = leanh::lean_ctor_get(v_c_3765_, 0);
                v_pos_3768_ = leanh::lean_ctor_get(v_s_3766_, 2);
                v___x_3772_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3767_, v_pos_3768_);
                if v___x_3772_ == 0 {
                    v_inputString_3773_ = leanh::lean_ctor_get(v_toInputContext_3767_, 0);
                    v_curr_3774_ = lean_string_utf8_get_fast(v_inputString_3773_, v_pos_3768_);
                    v___x_3775_ = 101;
                    v___x_3776_ = lean_uint32_dec_eq(v_curr_3774_, v___x_3775_);
                    if v___x_3776_ == 0 {
                        v___x_3777_ = 69;
                        v___x_3778_ = lean_uint32_dec_eq(v_curr_3774_, v___x_3777_);
                        if v___x_3778_ == 0 {
                            return v_s_3766_;
                        } else {
                            leanh::lean_inc(v_pos_3768_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3768_);
                        state = 1;
                        continue;
                    }
                } else {
                    return v_s_3766_;
                }
            }
            1 => {
                v___x_3770_ =
                    l_Lean_Parser_ParserState_next_x27___redArg(v_s_3766_, v_c_3765_, v_pos_3768_);
                leanh::lean_dec(v_pos_3768_);
                v___x_3771_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_3765_, v___x_3770_);
                return v___x_3771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(
    mut v_c_3779_: *mut leanh::LeanObject,
    mut v_s_3780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3781_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_3779_, v_s_3780_);
    leanh::lean_dec_ref(v_c_3779_);
    return v_res_3781_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(
    mut v_startPos_3799_: *mut leanh::LeanObject,
    mut v_curr_3800_: u32,
    mut v_nextPos_3801_: *mut leanh::LeanObject,
    mut v_c_3802_: *mut leanh::LeanObject,
    mut v_s_3803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: u32 = 0;
    let mut v___x_3810_: u8 = 0;
    let mut v_s_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: u32 = 0;
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: u32 = 0;
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u32 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: u8 = 0;
    let mut v_errorMsg_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3809_ = 46;
                v___x_3810_ = lean_uint32_dec_eq(v_curr_3800_, v___x_3809_);
                if v___x_3810_ == 0 {
                    v___x_3820_ = 101;
                    v___x_3821_ = lean_uint32_dec_eq(v_curr_3800_, v___x_3820_);
                    if v___x_3821_ == 0 {
                        v___x_3822_ = 69;
                        v___x_3823_ = lean_uint32_dec_eq(v_curr_3800_, v___x_3822_);
                        if v___x_3823_ == 0 {
                            leanh::lean_dec(v_nextPos_3801_);
                            v___x_3824_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
                            v___x_3825_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                            v___x_3826_ = l_Lake_Toml_pushLit(
                                v___x_3824_,
                                v_startPos_3799_,
                                v___x_3825_,
                                v_c_3802_,
                                v_s_3803_,
                            );
                            return v___x_3826_;
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    v___f_3827_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0;
                    v_s_3828_ = l_Lean_Parser_ParserState_setPos(v_s_3803_, v_nextPos_3801_);
                    v___x_3829_ = 95;
                    v___x_3830_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8;
                    v_s_3831_ = l_Lake_Toml_sepByChar1Fn(
                        v___f_3827_,
                        v___x_3829_,
                        v___x_3830_,
                        v_c_3802_,
                        v_s_3828_,
                    );
                    v_errorMsg_3837_ = leanh::lean_ctor_get(v_s_3831_, 4);
                    leanh::lean_inc(v_errorMsg_3837_);
                    v___x_3838_ = leanh::lean_box(0);
                    v___x_3839_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3837_,
                        v___x_3838_,
                    );
                    if v___x_3839_ == 0 {
                        if v___x_3810_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_c_3802_);
                            leanh::lean_dec(v_startPos_3799_);
                            return v_s_3831_;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3806_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
                v___x_3807_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                v___x_3808_ = l_Lake_Toml_pushLit(
                    v___x_3806_,
                    v_startPos_3799_,
                    v___x_3807_,
                    v_c_3802_,
                    v___y_3805_,
                );
                return v___x_3808_;
            }
            2 => {
                v_s_3812_ = l_Lean_Parser_ParserState_setPos(v_s_3803_, v_nextPos_3801_);
                v_s_3813_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_3802_, v_s_3812_);
                v_errorMsg_3814_ = leanh::lean_ctor_get(v_s_3813_, 4);
                leanh::lean_inc(v_errorMsg_3814_);
                v___x_3815_ = leanh::lean_box(0);
                v___x_3816_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                    v_errorMsg_3814_,
                    v___x_3815_,
                );
                if v___x_3816_ == 0 {
                    leanh::lean_dec_ref(v_c_3802_);
                    leanh::lean_dec(v_startPos_3799_);
                    return v_s_3813_;
                } else {
                    if v___x_3810_ == 0 {
                        v___x_3817_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
                        v___x_3818_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                        v___x_3819_ = l_Lake_Toml_pushLit(
                            v___x_3817_,
                            v_startPos_3799_,
                            v___x_3818_,
                            v_c_3802_,
                            v_s_3813_,
                        );
                        return v___x_3819_;
                    } else {
                        leanh::lean_dec_ref(v_c_3802_);
                        leanh::lean_dec(v_startPos_3799_);
                        return v_s_3813_;
                    }
                }
            }
            3 => {
                v_s_3833_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_3802_, v_s_3831_);
                v_errorMsg_3834_ = leanh::lean_ctor_get(v_s_3833_, 4);
                leanh::lean_inc(v_errorMsg_3834_);
                v___x_3835_ = leanh::lean_box(0);
                v___x_3836_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                    v_errorMsg_3834_,
                    v___x_3835_,
                );
                if v___x_3836_ == 0 {
                    if v___x_3810_ == 0 {
                        v___y_3805_ = v_s_3833_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_c_3802_);
                        leanh::lean_dec(v_startPos_3799_);
                        return v_s_3833_;
                    }
                } else {
                    v___y_3805_ = v_s_3833_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(
    mut v_startPos_3840_: *mut leanh::LeanObject,
    mut v_curr_3841_: *mut leanh::LeanObject,
    mut v_nextPos_3842_: *mut leanh::LeanObject,
    mut v_c_3843_: *mut leanh::LeanObject,
    mut v_s_3844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_curr_boxed_3845_: u32 = 0;
    let mut v_res_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_curr_boxed_3845_ = leanh::lean_unbox_uint32(v_curr_3841_);
    leanh::lean_dec(v_curr_3841_);
    v_res_3846_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(
        v_startPos_3840_,
        v_curr_boxed_3845_,
        v_nextPos_3842_,
        v_c_3843_,
        v_s_3844_,
    );
    return v_res_3846_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(
    mut v_startPos_3847_: *mut leanh::LeanObject,
    mut v_c_3848_: *mut leanh::LeanObject,
    mut v_s_3849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: u8 = 0;
    v_toInputContext_3850_ = leanh::lean_ctor_get(v_c_3848_, 0);
    v_pos_3851_ = leanh::lean_ctor_get(v_s_3849_, 2);
    v___x_3852_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3850_, v_pos_3851_);
    if v___x_3852_ == 0 {
        let mut v_inputString_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3854_: u32 = 0;
        let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_inputString_3853_ = leanh::lean_ctor_get(v_toInputContext_3850_, 0);
        v___x_3854_ = lean_string_utf8_get_fast(v_inputString_3853_, v_pos_3851_);
        v___x_3855_ = lean_string_utf8_next_fast(v_inputString_3853_, v_pos_3851_);
        v___x_3856_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(
            v_startPos_3847_,
            v___x_3854_,
            v___x_3855_,
            v_c_3848_,
            v_s_3849_,
        );
        return v___x_3856_;
    } else {
        let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3857_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
        v___x_3858_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
        v___x_3859_ = l_Lake_Toml_pushLit(
            v___x_3857_,
            v_startPos_3847_,
            v___x_3858_,
            v_c_3848_,
            v_s_3849_,
        );
        return v___x_3859_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(
    mut v_startPos_3867_: *mut leanh::LeanObject,
    mut v_c_3868_: *mut leanh::LeanObject,
    mut v_s_3869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u8 = 0;
    let mut v_inputString_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3874_: u32 = 0;
    let mut v___y_3876_: u8 = 0;
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u32 = 0;
    let mut v___x_3882_: u8 = 0;
    let mut v___x_3883_: u32 = 0;
    let mut v___x_3884_: u8 = 0;
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3870_ = leanh::lean_ctor_get(v_c_3868_, 0);
                v_pos_3871_ = leanh::lean_ctor_get(v_s_3869_, 2);
                v___x_3872_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3870_, v_pos_3871_);
                if v___x_3872_ == 0 {
                    v_inputString_3873_ = leanh::lean_ctor_get(v_toInputContext_3870_, 0);
                    v_curr_3874_ = lean_string_utf8_get_fast(v_inputString_3873_, v_pos_3871_);
                    v___x_3881_ = 48;
                    v___x_3882_ = lean_uint32_dec_le(v___x_3881_, v_curr_3874_);
                    if v___x_3882_ == 0 {
                        v___y_3876_ = v___x_3882_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3883_ = 57;
                        v___x_3884_ = lean_uint32_dec_le(v_curr_3874_, v___x_3883_);
                        v___y_3876_ = v___x_3884_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3885_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
                    v___x_3886_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                    v___x_3887_ = l_Lake_Toml_pushLit(
                        v___x_3885_,
                        v_startPos_3867_,
                        v___x_3886_,
                        v_c_3868_,
                        v_s_3869_,
                    );
                    return v___x_3887_;
                }
            }
            1 => {
                if v___y_3876_ == 0 {
                    v___x_3877_ = lean_string_utf8_next_fast(v_inputString_3873_, v_pos_3871_);
                    v___x_3878_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(
                        v_startPos_3867_,
                        v_curr_3874_,
                        v___x_3877_,
                        v_c_3868_,
                        v_s_3869_,
                    );
                    return v___x_3878_;
                } else {
                    leanh::lean_inc(v_pos_3871_);
                    v_s_3879_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3869_,
                        v_c_3868_,
                        v_pos_3871_,
                    );
                    leanh::lean_dec(v_pos_3871_);
                    v_s_3869_ = v_s_3879_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(
    mut v_startPos_3888_: *mut leanh::LeanObject,
    mut v_c_3889_: *mut leanh::LeanObject,
    mut v_s_3890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: u8 = 0;
    let mut v_inputString_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: u8 = 0;
    let mut v_curr_3897_: u32 = 0;
    let mut v___y_3899_: u8 = 0;
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: u32 = 0;
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: u32 = 0;
    let mut v___x_3906_: u8 = 0;
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_3891_ = leanh::lean_ctor_get(v_s_3890_, 2);
                v_toInputContext_3892_ = leanh::lean_ctor_get(v_c_3889_, 0);
                v_expected_3893_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2;
                v___x_3894_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3892_, v_pos_3891_);
                if v___x_3894_ == 0 {
                    v_inputString_3895_ = leanh::lean_ctor_get(v_toInputContext_3892_, 0);
                    v___x_3896_ = 1;
                    v_curr_3897_ = lean_string_utf8_get_fast(v_inputString_3895_, v_pos_3891_);
                    v___x_3903_ = 48;
                    v___x_3904_ = lean_uint32_dec_le(v___x_3903_, v_curr_3897_);
                    if v___x_3904_ == 0 {
                        v___y_3899_ = v___x_3904_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3905_ = 57;
                        v___x_3906_ = lean_uint32_dec_le(v_curr_3897_, v___x_3905_);
                        v___y_3899_ = v___x_3906_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_c_3889_);
                    leanh::lean_dec(v_startPos_3888_);
                    v___x_3907_ = l_Lean_Parser_ParserState_mkEOIError(v_s_3890_, v_expected_3893_);
                    return v___x_3907_;
                }
            }
            1 => {
                if v___y_3899_ == 0 {
                    leanh::lean_dec_ref(v_c_3889_);
                    leanh::lean_dec(v_startPos_3888_);
                    v___x_3900_ = l_Lake_Toml_mkUnexpectedCharError(
                        v_s_3890_,
                        v_curr_3897_,
                        v_expected_3893_,
                        v___x_3896_,
                    );
                    return v___x_3900_;
                } else {
                    leanh::lean_inc(v_pos_3891_);
                    v_s_3901_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3890_,
                        v_c_3889_,
                        v_pos_3891_,
                    );
                    leanh::lean_dec(v_pos_3891_);
                    v___x_3902_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(
                        v_startPos_3888_,
                        v_c_3889_,
                        v_s_3901_,
                    );
                    return v___x_3902_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(
    mut v_startPos_3908_: *mut leanh::LeanObject,
    mut v_curr_3909_: u32,
    mut v_nextPos_3910_: *mut leanh::LeanObject,
    mut v_c_3911_: *mut leanh::LeanObject,
    mut v_s_3912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3913_: u32 = 0;
    let mut v___x_3914_: u8 = 0;
    v___x_3913_ = 95;
    v___x_3914_ = lean_uint32_dec_eq(v_curr_3909_, v___x_3913_);
    if v___x_3914_ == 0 {
        let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3915_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(
            v_startPos_3908_,
            v_curr_3909_,
            v_nextPos_3910_,
            v_c_3911_,
            v_s_3912_,
        );
        return v___x_3915_;
    } else {
        let mut v_s_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_3916_ = l_Lean_Parser_ParserState_setPos(v_s_3912_, v_nextPos_3910_);
        v___x_3917_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(
            v_startPos_3908_,
            v_c_3911_,
            v_s_3916_,
        );
        return v___x_3917_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(
    mut v_startPos_3918_: *mut leanh::LeanObject,
    mut v_curr_3919_: *mut leanh::LeanObject,
    mut v_nextPos_3920_: *mut leanh::LeanObject,
    mut v_c_3921_: *mut leanh::LeanObject,
    mut v_s_3922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_curr_boxed_3923_: u32 = 0;
    let mut v_res_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_curr_boxed_3923_ = leanh::lean_unbox_uint32(v_curr_3919_);
    leanh::lean_dec(v_curr_3919_);
    v_res_3924_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(
        v_startPos_3918_,
        v_curr_boxed_3923_,
        v_nextPos_3920_,
        v_c_3921_,
        v_s_3922_,
    );
    return v_res_3924_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(
    mut v_startPos_3930_: *mut leanh::LeanObject,
    mut v_a_3931_: *mut leanh::LeanObject,
    mut v_a_3932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: u8 = 0;
    v___x_3933_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0;
    v___x_3934_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2;
    leanh::lean_inc_ref(v_a_3931_);
    v_s_3935_ = l_Lake_Toml_strFn(v___x_3933_, v___x_3934_, v_a_3931_, v_a_3932_);
    v_errorMsg_3936_ = leanh::lean_ctor_get(v_s_3935_, 4);
    leanh::lean_inc(v_errorMsg_3936_);
    v___x_3937_ = leanh::lean_box(0);
    v___x_3938_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3936_, v___x_3937_);
    if v___x_3938_ == 0 {
        leanh::lean_dec_ref(v_a_3931_);
        leanh::lean_dec(v_startPos_3930_);
        return v_s_3935_;
    } else {
        let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3939_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
        v___x_3940_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
        v___x_3941_ = l_Lake_Toml_pushLit(
            v___x_3939_,
            v_startPos_3930_,
            v___x_3940_,
            v_a_3931_,
            v_s_3935_,
        );
        return v___x_3941_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(
    mut v_startPos_3947_: *mut leanh::LeanObject,
    mut v_a_3948_: *mut leanh::LeanObject,
    mut v_a_3949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: u8 = 0;
    v___x_3950_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0;
    v___x_3951_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2;
    leanh::lean_inc_ref(v_a_3948_);
    v_s_3952_ = l_Lake_Toml_strFn(v___x_3950_, v___x_3951_, v_a_3948_, v_a_3949_);
    v_errorMsg_3953_ = leanh::lean_ctor_get(v_s_3952_, 4);
    leanh::lean_inc(v_errorMsg_3953_);
    v___x_3954_ = leanh::lean_box(0);
    v___x_3955_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3953_, v___x_3954_);
    if v___x_3955_ == 0 {
        leanh::lean_dec_ref(v_a_3948_);
        leanh::lean_dec(v_startPos_3947_);
        return v_s_3952_;
    } else {
        let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3956_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
        v___x_3957_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
        v___x_3958_ = l_Lake_Toml_pushLit(
            v___x_3956_,
            v_startPos_3947_,
            v___x_3957_,
            v_a_3948_,
            v_s_3952_,
        );
        return v___x_3958_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(
    mut v_startPos_3959_: *mut leanh::LeanObject,
    mut v_c_3960_: *mut leanh::LeanObject,
    mut v_s_3961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInputContext_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v_inputString_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3967_: u32 = 0;
    let mut v___x_3968_: u32 = 0;
    let mut v___x_3969_: u8 = 0;
    let mut v___x_3970_: u8 = 0;
    let mut v___y_3972_: u8 = 0;
    let mut v___x_3973_: u32 = 0;
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3975_: u32 = 0;
    let mut v___x_3976_: u8 = 0;
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: u32 = 0;
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3962_ = leanh::lean_ctor_get(v_c_3960_, 0);
                v_pos_3963_ = leanh::lean_ctor_get(v_s_3961_, 2);
                v_expected_3964_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2;
                v___x_3965_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3962_, v_pos_3963_);
                if v___x_3965_ == 0 {
                    v_inputString_3966_ = leanh::lean_ctor_get(v_toInputContext_3962_, 0);
                    v_curr_3967_ = lean_string_utf8_get_fast(v_inputString_3966_, v_pos_3963_);
                    v___x_3968_ = 48;
                    v___x_3969_ = lean_uint32_dec_eq(v_curr_3967_, v___x_3968_);
                    if v___x_3969_ == 0 {
                        v___x_3970_ = 1;
                        v___x_3984_ = lean_uint32_dec_le(v___x_3968_, v_curr_3967_);
                        if v___x_3984_ == 0 {
                            v___y_3972_ = v___x_3984_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3985_ = 57;
                            v___x_3986_ = lean_uint32_dec_le(v_curr_3967_, v___x_3985_);
                            v___y_3972_ = v___x_3986_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3963_);
                        v___x_3987_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3961_,
                            v_c_3960_,
                            v_pos_3963_,
                        );
                        leanh::lean_dec(v_pos_3963_);
                        v___x_3988_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(
                            v_startPos_3959_,
                            v_c_3960_,
                            v___x_3987_,
                        );
                        return v___x_3988_;
                    }
                } else {
                    leanh::lean_dec_ref(v_c_3960_);
                    leanh::lean_dec(v_startPos_3959_);
                    v___x_3989_ = l_Lean_Parser_ParserState_mkEOIError(v_s_3961_, v_expected_3964_);
                    return v___x_3989_;
                }
            }
            1 => {
                if v___y_3972_ == 0 {
                    v___x_3973_ = 105;
                    v___x_3974_ = lean_uint32_dec_eq(v_curr_3967_, v___x_3973_);
                    if v___x_3974_ == 0 {
                        v___x_3975_ = 110;
                        v___x_3976_ = lean_uint32_dec_eq(v_curr_3967_, v___x_3975_);
                        if v___x_3976_ == 0 {
                            leanh::lean_dec_ref(v_c_3960_);
                            leanh::lean_dec(v_startPos_3959_);
                            v___x_3977_ = l_Lake_Toml_mkUnexpectedCharError(
                                v_s_3961_,
                                v_curr_3967_,
                                v_expected_3964_,
                                v___x_3970_,
                            );
                            return v___x_3977_;
                        } else {
                            leanh::lean_inc(v_pos_3963_);
                            v___x_3978_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_3961_,
                                v_c_3960_,
                                v_pos_3963_,
                            );
                            leanh::lean_dec(v_pos_3963_);
                            v___x_3979_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(
                                v_startPos_3959_,
                                v_c_3960_,
                                v___x_3978_,
                            );
                            return v___x_3979_;
                        }
                    } else {
                        leanh::lean_inc(v_pos_3963_);
                        v___x_3980_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3961_,
                            v_c_3960_,
                            v_pos_3963_,
                        );
                        leanh::lean_dec(v_pos_3963_);
                        v___x_3981_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(
                            v_startPos_3959_,
                            v_c_3960_,
                            v___x_3980_,
                        );
                        return v___x_3981_;
                    }
                } else {
                    leanh::lean_inc(v_pos_3963_);
                    v___x_3982_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3961_,
                        v_c_3960_,
                        v_pos_3963_,
                    );
                    leanh::lean_dec(v_pos_3963_);
                    v___x_3983_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(
                        v_startPos_3959_,
                        v_c_3960_,
                        v___x_3982_,
                    );
                    return v___x_3983_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(
    mut v_startPos_4005_: *mut leanh::LeanObject,
    mut v_c_4006_: *mut leanh::LeanObject,
    mut v_s_4007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4011_: u32 = 0;
    let mut v___y_4012_: u8 = 0;
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4018_: u8 = 0;
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4024_: u8 = 0;
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v_inputString_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: u32 = 0;
    let mut v___y_4036_: u8 = 0;
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v_pos_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_4041_: u32 = 0;
    let mut v_nextPos_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: u32 = 0;
    let mut v___x_4044_: u8 = 0;
    let mut v___x_4045_: u32 = 0;
    let mut v___x_4046_: u8 = 0;
    let mut v___x_4047_: u32 = 0;
    let mut v___x_4048_: u8 = 0;
    let mut v_s_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: u32 = 0;
    let mut v___y_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4061_: u8 = 0;
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    let mut v_curr_4066_: u32 = 0;
    let mut v_nextPos_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: u32 = 0;
    let mut v___x_4069_: u8 = 0;
    let mut v___x_4070_: u32 = 0;
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_4075_: u32 = 0;
    let mut v_nextPos_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4078_: u8 = 0;
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: u8 = 0;
    let mut v_curr_4083_: u32 = 0;
    let mut v_nextPos_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u32 = 0;
    let mut v___x_4086_: u8 = 0;
    let mut v___x_4087_: u32 = 0;
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: u32 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v_s_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u32 = 0;
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: u32 = 0;
    let mut v___x_4102_: u8 = 0;
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_4028_ = leanh::lean_ctor_get(v_c_4006_, 0);
                v_pos_4029_ = leanh::lean_ctor_get(v_s_4007_, 2);
                v___x_4030_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4028_, v_pos_4029_);
                if v___x_4030_ == 0 {
                    v_inputString_4031_ = leanh::lean_ctor_get(v_toInputContext_4028_, 0);
                    v_curr_4075_ = lean_string_utf8_get_fast(v_inputString_4031_, v_pos_4029_);
                    v_nextPos_4076_ = lean_string_utf8_next_fast(v_inputString_4031_, v_pos_4029_);
                    v___x_4099_ = 48;
                    v___x_4100_ = lean_uint32_dec_le(v___x_4099_, v_curr_4075_);
                    if v___x_4100_ == 0 {
                        v___y_4078_ = v___x_4100_;
                        state = 6;
                        continue;
                    } else {
                        v___x_4101_ = 57;
                        v___x_4102_ = lean_uint32_dec_le(v_curr_4075_, v___x_4101_);
                        v___y_4078_ = v___x_4102_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_c_4006_);
                    leanh::lean_dec(v_startPos_4005_);
                    v___x_4103_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5;
                    v___x_4104_ = l_Lean_Parser_ParserState_mkEOIError(v_s_4007_, v___x_4103_);
                    return v___x_4104_;
                }
            }
            1 => {
                if v___y_4012_ == 0 {
                    v___x_4013_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(
                        v_startPos_4005_,
                        v___y_4011_,
                        v___y_4010_,
                        v_c_4006_,
                        v___y_4009_,
                    );
                    return v___x_4013_;
                } else {
                    v_s_4014_ = l_Lean_Parser_ParserState_setPos(v___y_4009_, v___y_4010_);
                    v___x_4015_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(
                        v_startPos_4005_,
                        v_c_4006_,
                        v_s_4014_,
                    );
                    return v___x_4015_;
                }
            }
            2 => {
                if v___y_4018_ == 0 {
                    v___x_4019_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
                    v___x_4020_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                    v___x_4021_ = l_Lake_Toml_pushLit(
                        v___x_4019_,
                        v_startPos_4005_,
                        v___x_4020_,
                        v_c_4006_,
                        v___y_4017_,
                    );
                    return v___x_4021_;
                } else {
                    leanh::lean_dec_ref(v_c_4006_);
                    leanh::lean_dec(v_startPos_4005_);
                    return v___y_4017_;
                }
            }
            3 => {
                if v___y_4024_ == 0 {
                    v___x_4025_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
                    v___x_4026_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                    v___x_4027_ = l_Lake_Toml_pushLit(
                        v___x_4025_,
                        v_startPos_4005_,
                        v___x_4026_,
                        v_c_4006_,
                        v___y_4023_,
                    );
                    return v___x_4027_;
                } else {
                    leanh::lean_dec_ref(v_c_4006_);
                    leanh::lean_dec(v_startPos_4005_);
                    return v___y_4023_;
                }
            }
            4 => {
                if v___y_4036_ == 0 {
                    v___x_4037_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(
                        v_startPos_4005_,
                        v___y_4035_,
                        v___y_4033_,
                        v_c_4006_,
                        v___y_4034_,
                    );
                    return v___x_4037_;
                } else {
                    leanh::lean_inc(v___y_4033_);
                    v_s_4038_ = l_Lean_Parser_ParserState_setPos(v___y_4034_, v___y_4033_);
                    v___x_4039_ =
                        l_Lean_Parser_InputContext_atEnd(v_toInputContext_4028_, v___y_4033_);
                    leanh::lean_dec(v___y_4033_);
                    if v___x_4039_ == 0 {
                        v_pos_4040_ = leanh::lean_ctor_get(v_s_4038_, 2);
                        leanh::lean_inc(v_pos_4040_);
                        v_curr_4041_ = lean_string_utf8_get_fast(v_inputString_4031_, v_pos_4040_);
                        v_nextPos_4042_ =
                            lean_string_utf8_next_fast(v_inputString_4031_, v_pos_4040_);
                        leanh::lean_dec(v_pos_4040_);
                        v___x_4043_ = 45;
                        v___x_4044_ = lean_uint32_dec_eq(v_curr_4041_, v___x_4043_);
                        if v___x_4044_ == 0 {
                            v___x_4045_ = 48;
                            v___x_4046_ = lean_uint32_dec_le(v___x_4045_, v_curr_4041_);
                            if v___x_4046_ == 0 {
                                v___y_4009_ = v_s_4038_;
                                v___y_4010_ = v_nextPos_4042_;
                                v___y_4011_ = v_curr_4041_;
                                v___y_4012_ = v___x_4046_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4047_ = 57;
                                v___x_4048_ = lean_uint32_dec_le(v_curr_4041_, v___x_4047_);
                                v___y_4009_ = v_s_4038_;
                                v___y_4010_ = v_nextPos_4042_;
                                v___y_4011_ = v_curr_4041_;
                                v___y_4012_ = v___x_4048_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_s_4049_ =
                                l_Lean_Parser_ParserState_setPos(v_s_4038_, v_nextPos_4042_);
                            v_s_4050_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(
                                v_c_4006_, v_s_4049_,
                            );
                            v_errorMsg_4051_ = leanh::lean_ctor_get(v_s_4050_, 4);
                            leanh::lean_inc(v_errorMsg_4051_);
                            v___x_4052_ = leanh::lean_box(0);
                            v___x_4053_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                v_errorMsg_4051_,
                                v___x_4052_,
                            );
                            if v___x_4053_ == 0 {
                                v___y_4017_ = v_s_4050_;
                                v___y_4018_ = v___x_4044_;
                                state = 2;
                                continue;
                            } else {
                                v___y_4017_ = v_s_4050_;
                                v___y_4018_ = v___x_4039_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___x_4054_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
                        v___x_4055_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                        v___x_4056_ = l_Lake_Toml_pushLit(
                            v___x_4054_,
                            v_startPos_4005_,
                            v___x_4055_,
                            v_c_4006_,
                            v_s_4038_,
                        );
                        return v___x_4056_;
                    }
                }
            }
            5 => {
                if v___y_4061_ == 0 {
                    v___x_4062_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(
                        v_startPos_4005_,
                        v___y_4059_,
                        v___y_4060_,
                        v_c_4006_,
                        v___y_4058_,
                    );
                    return v___x_4062_;
                } else {
                    v_s_4063_ = l_Lean_Parser_ParserState_setPos(v___y_4058_, v___y_4060_);
                    v_pos_4064_ = leanh::lean_ctor_get(v_s_4063_, 2);
                    leanh::lean_inc(v_pos_4064_);
                    v___x_4065_ =
                        l_Lean_Parser_InputContext_atEnd(v_toInputContext_4028_, v_pos_4064_);
                    if v___x_4065_ == 0 {
                        v_curr_4066_ = lean_string_utf8_get_fast(v_inputString_4031_, v_pos_4064_);
                        v_nextPos_4067_ =
                            lean_string_utf8_next_fast(v_inputString_4031_, v_pos_4064_);
                        leanh::lean_dec(v_pos_4064_);
                        v___x_4068_ = 48;
                        v___x_4069_ = lean_uint32_dec_le(v___x_4068_, v_curr_4066_);
                        if v___x_4069_ == 0 {
                            v___y_4033_ = v_nextPos_4067_;
                            v___y_4034_ = v_s_4063_;
                            v___y_4035_ = v_curr_4066_;
                            v___y_4036_ = v___x_4069_;
                            state = 4;
                            continue;
                        } else {
                            v___x_4070_ = 57;
                            v___x_4071_ = lean_uint32_dec_le(v_curr_4066_, v___x_4070_);
                            v___y_4033_ = v_nextPos_4067_;
                            v___y_4034_ = v_s_4063_;
                            v___y_4035_ = v_curr_4066_;
                            v___y_4036_ = v___x_4071_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_pos_4064_);
                        v___x_4072_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
                        v___x_4073_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                        v___x_4074_ = l_Lake_Toml_pushLit(
                            v___x_4072_,
                            v_startPos_4005_,
                            v___x_4073_,
                            v_c_4006_,
                            v_s_4063_,
                        );
                        return v___x_4074_;
                    }
                }
            }
            6 => {
                if v___y_4078_ == 0 {
                    v___x_4079_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(
                        v_startPos_4005_,
                        v_curr_4075_,
                        v_nextPos_4076_,
                        v_c_4006_,
                        v_s_4007_,
                    );
                    return v___x_4079_;
                } else {
                    v_s_4080_ = l_Lean_Parser_ParserState_setPos(v_s_4007_, v_nextPos_4076_);
                    v_pos_4081_ = leanh::lean_ctor_get(v_s_4080_, 2);
                    leanh::lean_inc(v_pos_4081_);
                    v___x_4082_ =
                        l_Lean_Parser_InputContext_atEnd(v_toInputContext_4028_, v_pos_4081_);
                    if v___x_4082_ == 0 {
                        v_curr_4083_ = lean_string_utf8_get_fast(v_inputString_4031_, v_pos_4081_);
                        v_nextPos_4084_ =
                            lean_string_utf8_next_fast(v_inputString_4031_, v_pos_4081_);
                        leanh::lean_dec(v_pos_4081_);
                        v___x_4085_ = 58;
                        v___x_4086_ = lean_uint32_dec_eq(v_curr_4083_, v___x_4085_);
                        if v___x_4086_ == 0 {
                            v___x_4087_ = 48;
                            v___x_4088_ = lean_uint32_dec_le(v___x_4087_, v_curr_4083_);
                            if v___x_4088_ == 0 {
                                v___y_4058_ = v_s_4080_;
                                v___y_4059_ = v_curr_4083_;
                                v___y_4060_ = v_nextPos_4084_;
                                v___y_4061_ = v___x_4088_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4089_ = 57;
                                v___x_4090_ = lean_uint32_dec_le(v_curr_4083_, v___x_4089_);
                                v___y_4058_ = v_s_4080_;
                                v___y_4059_ = v_curr_4083_;
                                v___y_4060_ = v_nextPos_4084_;
                                v___y_4061_ = v___x_4090_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_s_4091_ =
                                l_Lean_Parser_ParserState_setPos(v_s_4080_, v_nextPos_4084_);
                            v_s_4092_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(
                                v___x_4082_,
                                v_c_4006_,
                                v_s_4091_,
                            );
                            v_errorMsg_4093_ = leanh::lean_ctor_get(v_s_4092_, 4);
                            leanh::lean_inc(v_errorMsg_4093_);
                            v___x_4094_ = leanh::lean_box(0);
                            v___x_4095_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                v_errorMsg_4093_,
                                v___x_4094_,
                            );
                            if v___x_4095_ == 0 {
                                v___y_4023_ = v_s_4092_;
                                v___y_4024_ = v___x_4086_;
                                state = 3;
                                continue;
                            } else {
                                v___y_4023_ = v_s_4092_;
                                v___y_4024_ = v___x_4082_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_pos_4081_);
                        v___x_4096_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
                        v___x_4097_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                        v___x_4098_ = l_Lake_Toml_pushLit(
                            v___x_4096_,
                            v_startPos_4005_,
                            v___x_4097_,
                            v_c_4006_,
                            v_s_4080_,
                        );
                        return v___x_4098_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_numeralFn___lam__0(
    mut v_c_4140_: *mut leanh::LeanObject,
    mut v_s_4141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: u8 = 0;
    let mut v_inputString_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_4150_: u32 = 0;
    let mut v___x_4151_: u32 = 0;
    let mut v___x_4152_: u8 = 0;
    let mut v___x_4153_: u8 = 0;
    let mut v___y_4155_: u8 = 0;
    let mut v___x_4156_: u32 = 0;
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4158_: u32 = 0;
    let mut v___x_4159_: u8 = 0;
    let mut v___x_4160_: u32 = 0;
    let mut v___x_4161_: u8 = 0;
    let mut v___x_4162_: u32 = 0;
    let mut v___x_4163_: u8 = 0;
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4178_: u32 = 0;
    let mut v___x_4179_: u8 = 0;
    let mut v_s_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: u8 = 0;
    let mut v_curr_4183_: u32 = 0;
    let mut v___x_4184_: u32 = 0;
    let mut v___x_4185_: u8 = 0;
    let mut v___x_4186_: u32 = 0;
    let mut v___x_4187_: u8 = 0;
    let mut v___x_4188_: u32 = 0;
    let mut v___x_4189_: u8 = 0;
    let mut v___y_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: u8 = 0;
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4199_: u8 = 0;
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u32 = 0;
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: u8 = 0;
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: u8 = 0;
    let mut v___x_4211_: u32 = 0;
    let mut v___x_4212_: u8 = 0;
    let mut v_s_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: u32 = 0;
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4219_: u8 = 0;
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: u8 = 0;
    let mut v_s_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u32 = 0;
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4232_: u8 = 0;
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: u8 = 0;
    let mut v_s_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: u32 = 0;
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4245_: u8 = 0;
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_4142_ = leanh::lean_ctor_get(v_s_4141_, 2);
                v_toInputContext_4146_ = leanh::lean_ctor_get(v_c_4140_, 0);
                v_expected_4147_ = l_Lake_Toml_numeralFn___lam__0___closed__1;
                v___x_4148_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4146_, v_pos_4142_);
                if v___x_4148_ == 0 {
                    v_inputString_4149_ = leanh::lean_ctor_get(v_toInputContext_4146_, 0);
                    v_curr_4150_ = lean_string_utf8_get_fast(v_inputString_4149_, v_pos_4142_);
                    v___x_4151_ = 48;
                    v___x_4152_ = lean_uint32_dec_eq(v_curr_4150_, v___x_4151_);
                    if v___x_4152_ == 0 {
                        v___x_4153_ = 1;
                        v___x_4177_ = lean_uint32_dec_le(v___x_4151_, v_curr_4150_);
                        if v___x_4177_ == 0 {
                            v___y_4155_ = v___x_4177_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4178_ = 57;
                            v___x_4179_ = lean_uint32_dec_le(v_curr_4150_, v___x_4178_);
                            v___y_4155_ = v___x_4179_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_pos_4142_);
                        v_s_4180_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_4141_,
                            v_c_4140_,
                            v_pos_4142_,
                        );
                        v_pos_4181_ = leanh::lean_ctor_get(v_s_4180_, 2);
                        leanh::lean_inc(v_pos_4181_);
                        v___x_4182_ =
                            l_Lean_Parser_InputContext_atEnd(v_toInputContext_4146_, v_pos_4181_);
                        if v___x_4182_ == 0 {
                            v_curr_4183_ =
                                lean_string_utf8_get_fast(v_inputString_4149_, v_pos_4181_);
                            v___x_4184_ = 98;
                            v___x_4185_ = lean_uint32_dec_eq(v_curr_4183_, v___x_4184_);
                            if v___x_4185_ == 0 {
                                v___x_4186_ = 111;
                                v___x_4187_ = lean_uint32_dec_eq(v_curr_4183_, v___x_4186_);
                                if v___x_4187_ == 0 {
                                    v___x_4188_ = 120;
                                    v___x_4189_ = lean_uint32_dec_eq(v_curr_4183_, v___x_4188_);
                                    if v___x_4189_ == 0 {
                                        v___x_4210_ = lean_uint32_dec_le(v___x_4151_, v_curr_4183_);
                                        if v___x_4210_ == 0 {
                                            v___y_4199_ = v___x_4210_;
                                            state = 4;
                                            continue;
                                        } else {
                                            v___x_4211_ = 57;
                                            v___x_4212_ =
                                                lean_uint32_dec_le(v_curr_4183_, v___x_4211_);
                                            v___y_4199_ = v___x_4212_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        v_s_4213_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                            v_s_4180_,
                                            v_c_4140_,
                                            v_pos_4181_,
                                        );
                                        leanh::lean_dec(v_pos_4181_);
                                        v___x_4214_ = l_Lake_Toml_numeralFn___lam__0___closed__3;
                                        v___x_4215_ = 95;
                                        v___x_4216_ = l_Lake_Toml_numeralFn___lam__0___closed__5;
                                        v_s_4217_ = l_Lake_Toml_sepByChar1Fn(
                                            v___x_4214_,
                                            v___x_4215_,
                                            v___x_4216_,
                                            v_c_4140_,
                                            v_s_4213_,
                                        );
                                        v_errorMsg_4223_ =
                                            leanh::lean_ctor_get(v_s_4217_, 4);
                                        leanh::lean_inc(v_errorMsg_4223_);
                                        v___x_4224_ = leanh::lean_box(0);
                                        v___x_4225_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_4223_, v___x_4224_);
                                        if v___x_4225_ == 0 {
                                            v___y_4219_ = v___x_4189_;
                                            state = 5;
                                            continue;
                                        } else {
                                            v___y_4219_ = v___x_4187_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_s_4226_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                        v_s_4180_,
                                        v_c_4140_,
                                        v_pos_4181_,
                                    );
                                    leanh::lean_dec(v_pos_4181_);
                                    v___x_4227_ = l_Lake_Toml_numeralFn___lam__0___closed__8;
                                    v___x_4228_ = 95;
                                    v___x_4229_ = l_Lake_Toml_numeralFn___lam__0___closed__10;
                                    v_s_4230_ = l_Lake_Toml_sepByChar1Fn(
                                        v___x_4227_,
                                        v___x_4228_,
                                        v___x_4229_,
                                        v_c_4140_,
                                        v_s_4226_,
                                    );
                                    v_errorMsg_4236_ = leanh::lean_ctor_get(v_s_4230_, 4);
                                    leanh::lean_inc(v_errorMsg_4236_);
                                    v___x_4237_ = leanh::lean_box(0);
                                    v___x_4238_ =
                                        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                            v_errorMsg_4236_,
                                            v___x_4237_,
                                        );
                                    if v___x_4238_ == 0 {
                                        v___y_4232_ = v___x_4187_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___y_4232_ = v___x_4185_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                v_s_4239_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_4180_,
                                    v_c_4140_,
                                    v_pos_4181_,
                                );
                                leanh::lean_dec(v_pos_4181_);
                                v___x_4240_ = l_Lake_Toml_numeralFn___lam__0___closed__13;
                                v___x_4241_ = 95;
                                v___x_4242_ = l_Lake_Toml_numeralFn___lam__0___closed__15;
                                v_s_4243_ = l_Lake_Toml_sepByChar1Fn(
                                    v___x_4240_,
                                    v___x_4241_,
                                    v___x_4242_,
                                    v_c_4140_,
                                    v_s_4239_,
                                );
                                v_errorMsg_4249_ = leanh::lean_ctor_get(v_s_4243_, 4);
                                leanh::lean_inc(v_errorMsg_4249_);
                                v___x_4250_ = leanh::lean_box(0);
                                v___x_4251_ =
                                    l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                        v_errorMsg_4249_,
                                        v___x_4250_,
                                    );
                                if v___x_4251_ == 0 {
                                    v___y_4245_ = v___x_4185_;
                                    state = 7;
                                    continue;
                                } else {
                                    v___y_4245_ = v___x_4182_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_pos_4181_);
                            v___x_4252_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
                            v___x_4253_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                            v___x_4254_ = l_Lake_Toml_pushLit(
                                v___x_4252_,
                                v_pos_4142_,
                                v___x_4253_,
                                v_c_4140_,
                                v_s_4180_,
                            );
                            return v___x_4254_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_c_4140_);
                    v___x_4255_ = l_Lean_Parser_ParserState_mkEOIError(v_s_4141_, v_expected_4147_);
                    return v___x_4255_;
                }
            }
            1 => {
                v___x_4144_ =
                    l_Lean_Parser_ParserState_next_x27___redArg(v_s_4141_, v_c_4140_, v_pos_4142_);
                v___x_4145_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(
                    v_pos_4142_,
                    v_c_4140_,
                    v___x_4144_,
                );
                return v___x_4145_;
            }
            2 => {
                if v___y_4155_ == 0 {
                    v___x_4156_ = 43;
                    v___x_4157_ = lean_uint32_dec_eq(v_curr_4150_, v___x_4156_);
                    if v___x_4157_ == 0 {
                        v___x_4158_ = 45;
                        v___x_4159_ = lean_uint32_dec_eq(v_curr_4150_, v___x_4158_);
                        if v___x_4159_ == 0 {
                            v___x_4160_ = 105;
                            v___x_4161_ = lean_uint32_dec_eq(v_curr_4150_, v___x_4160_);
                            if v___x_4161_ == 0 {
                                v___x_4162_ = 110;
                                v___x_4163_ = lean_uint32_dec_eq(v_curr_4150_, v___x_4162_);
                                if v___x_4163_ == 0 {
                                    leanh::lean_dec_ref(v_c_4140_);
                                    v___x_4164_ = l_Lake_Toml_numeralFn___lam__0___closed__2;
                                    v___x_4165_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
                                    v___x_4166_ = lean_string_push(v___x_4165_, v_curr_4150_);
                                    v___x_4167_ = lean_string_append(v___x_4164_, v___x_4166_);
                                    leanh::lean_dec_ref(v___x_4166_);
                                    v___x_4168_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
                                    v___x_4169_ = lean_string_append(v___x_4167_, v___x_4168_);
                                    v___x_4170_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                                        v_s_4141_,
                                        v___x_4169_,
                                        v_expected_4147_,
                                        v___x_4153_,
                                    );
                                    return v___x_4170_;
                                } else {
                                    leanh::lean_inc(v_pos_4142_);
                                    v___x_4171_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                        v_s_4141_,
                                        v_c_4140_,
                                        v_pos_4142_,
                                    );
                                    v___x_4172_ =
                                        l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(
                                            v_pos_4142_,
                                            v_c_4140_,
                                            v___x_4171_,
                                        );
                                    return v___x_4172_;
                                }
                            } else {
                                leanh::lean_inc(v_pos_4142_);
                                v___x_4173_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_4141_,
                                    v_c_4140_,
                                    v_pos_4142_,
                                );
                                v___x_4174_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(
                                    v_pos_4142_,
                                    v_c_4140_,
                                    v___x_4173_,
                                );
                                return v___x_4174_;
                            }
                        } else {
                            leanh::lean_inc(v_pos_4142_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_pos_4142_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_pos_4142_);
                    v___x_4175_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_4141_,
                        v_c_4140_,
                        v_pos_4142_,
                    );
                    v___x_4176_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(
                        v_pos_4142_,
                        v_c_4140_,
                        v___x_4175_,
                    );
                    return v___x_4176_;
                }
            }
            3 => {
                v_errorMsg_4192_ = leanh::lean_ctor_get(v___y_4191_, 4);
                v___x_4193_ = leanh::lean_box(0);
                leanh::lean_inc(v_errorMsg_4192_);
                v___x_4194_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                    v_errorMsg_4192_,
                    v___x_4193_,
                );
                if v___x_4194_ == 0 {
                    leanh::lean_dec(v_pos_4142_);
                    leanh::lean_dec_ref(v_c_4140_);
                    return v___y_4191_;
                } else {
                    if v___x_4189_ == 0 {
                        v___x_4195_ =
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
                        v___x_4196_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                        v___x_4197_ = l_Lake_Toml_pushLit(
                            v___x_4195_,
                            v_pos_4142_,
                            v___x_4196_,
                            v_c_4140_,
                            v___y_4191_,
                        );
                        return v___x_4197_;
                    } else {
                        leanh::lean_dec(v_pos_4142_);
                        leanh::lean_dec_ref(v_c_4140_);
                        return v___y_4191_;
                    }
                }
            }
            4 => {
                if v___y_4199_ == 0 {
                    v___x_4200_ = lean_string_utf8_next_fast(v_inputString_4149_, v_pos_4181_);
                    leanh::lean_dec(v_pos_4181_);
                    v___x_4201_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(
                        v_pos_4142_,
                        v_curr_4183_,
                        v___x_4200_,
                        v_c_4140_,
                        v_s_4180_,
                    );
                    return v___x_4201_;
                } else {
                    v_s_4202_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_4180_,
                        v_c_4140_,
                        v_pos_4181_,
                    );
                    leanh::lean_dec(v_pos_4181_);
                    v___x_4203_ = 58;
                    v___x_4204_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once
                        ),
                        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7,
                    );
                    v_s_4205_ = l_Lake_Toml_chFn(v___x_4203_, v___x_4204_, v_c_4140_, v_s_4202_);
                    v_errorMsg_4206_ = leanh::lean_ctor_get(v_s_4205_, 4);
                    leanh::lean_inc(v_errorMsg_4206_);
                    v___x_4207_ = leanh::lean_box(0);
                    v___x_4208_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_4206_,
                        v___x_4207_,
                    );
                    if v___x_4208_ == 0 {
                        v___y_4191_ = v_s_4205_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4209_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(
                            v___x_4189_,
                            v_c_4140_,
                            v_s_4205_,
                        );
                        v___y_4191_ = v___x_4209_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                if v___y_4219_ == 0 {
                    v___x_4220_ = l_Lake_Toml_numeralFn___lam__0___closed__7;
                    v___x_4221_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                    v___x_4222_ = l_Lake_Toml_pushLit(
                        v___x_4220_,
                        v_pos_4142_,
                        v___x_4221_,
                        v_c_4140_,
                        v_s_4217_,
                    );
                    return v___x_4222_;
                } else {
                    leanh::lean_dec(v_pos_4142_);
                    leanh::lean_dec_ref(v_c_4140_);
                    return v_s_4217_;
                }
            }
            6 => {
                if v___y_4232_ == 0 {
                    v___x_4233_ = l_Lake_Toml_numeralFn___lam__0___closed__12;
                    v___x_4234_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                    v___x_4235_ = l_Lake_Toml_pushLit(
                        v___x_4233_,
                        v_pos_4142_,
                        v___x_4234_,
                        v_c_4140_,
                        v_s_4230_,
                    );
                    return v___x_4235_;
                } else {
                    leanh::lean_dec(v_pos_4142_);
                    leanh::lean_dec_ref(v_c_4140_);
                    return v_s_4230_;
                }
            }
            7 => {
                if v___y_4245_ == 0 {
                    v___x_4246_ = l_Lake_Toml_numeralFn___lam__0___closed__17;
                    v___x_4247_ =
                        l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
                    v___x_4248_ = l_Lake_Toml_pushLit(
                        v___x_4246_,
                        v_pos_4142_,
                        v___x_4247_,
                        v_c_4140_,
                        v_s_4243_,
                    );
                    return v___x_4248_;
                } else {
                    leanh::lean_dec(v_pos_4142_);
                    leanh::lean_dec_ref(v_c_4140_);
                    return v_s_4243_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_numeralFn(
    mut v_a_4257_: *mut leanh::LeanObject,
    mut v_a_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4259_ = l_Lake_Toml_numeralFn___closed__0;
    v___x_4260_ = l_Lean_Parser_atomicFn(v___f_4259_, v_a_4257_, v_a_4258_);
    return v___x_4260_;
}
pub unsafe fn _init_l_Lake_Toml_trailingWs___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4261_ =
        leanh::lean_alloc_closure(l_Lake_Toml_wsFn___boxed as *mut core::ffi::c_void, 2, 0);
    v___x_4262_ = l_Lake_Toml_trailing(v___x_4261_);
    return v___x_4262_;
}
pub unsafe fn _init_l_Lake_Toml_trailingWs() -> *mut leanh::LeanObject {
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4263_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_trailingWs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_trailingWs___closed__0_once),
        _init_l_Lake_Toml_trailingWs___closed__0,
    );
    return v___x_4263_;
}
pub unsafe fn _init_l_Lake_Toml_trailingSep___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4265_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4266_ = l_Lake_Toml_trailing(v___x_4265_);
    return v___x_4266_;
}
pub unsafe fn _init_l_Lake_Toml_trailingSep() -> *mut leanh::LeanObject {
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4267_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_trailingSep___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_trailingSep___closed__1_once),
        _init_l_Lake_Toml_trailingSep___closed__1,
    );
    return v___x_4267_;
}
pub unsafe fn l_Lake_Toml_unquotedKeyFn___lam__0(mut v_c_4268_: u32) -> u8 {
    let mut v___y_4270_: u8 = 0;
    let mut v___x_4271_: u32 = 0;
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: u32 = 0;
    let mut v___x_4274_: u8 = 0;
    let mut v___y_4276_: u8 = 0;
    let mut v___x_4277_: u32 = 0;
    let mut v___x_4278_: u8 = 0;
    let mut v___x_4279_: u32 = 0;
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4282_: u32 = 0;
    let mut v___x_4283_: u8 = 0;
    let mut v___x_4284_: u32 = 0;
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4286_: u32 = 0;
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: u32 = 0;
    let mut v___x_4289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4286_ = 65;
                v___x_4287_ = lean_uint32_dec_le(v___x_4286_, v_c_4268_);
                if v___x_4287_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v___x_4288_ = 90;
                    v___x_4289_ = lean_uint32_dec_le(v_c_4268_, v___x_4288_);
                    if v___x_4289_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        return v___x_4289_;
                    }
                }
            }
            1 => {
                if v___y_4270_ == 0 {
                    v___x_4271_ = 95;
                    v___x_4272_ = lean_uint32_dec_eq(v_c_4268_, v___x_4271_);
                    if v___x_4272_ == 0 {
                        v___x_4273_ = 45;
                        v___x_4274_ = lean_uint32_dec_eq(v_c_4268_, v___x_4273_);
                        return v___x_4274_;
                    } else {
                        return v___x_4272_;
                    }
                } else {
                    return v___y_4270_;
                }
            }
            2 => {
                if v___y_4276_ == 0 {
                    v___x_4277_ = 48;
                    v___x_4278_ = lean_uint32_dec_le(v___x_4277_, v_c_4268_);
                    if v___x_4278_ == 0 {
                        v___y_4270_ = v___x_4278_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4279_ = 57;
                        v___x_4280_ = lean_uint32_dec_le(v_c_4268_, v___x_4279_);
                        v___y_4270_ = v___x_4280_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_4276_;
                }
            }
            3 => {
                v___x_4282_ = 97;
                v___x_4283_ = lean_uint32_dec_le(v___x_4282_, v_c_4268_);
                if v___x_4283_ == 0 {
                    v___y_4276_ = v___x_4283_;
                    state = 2;
                    continue;
                } else {
                    v___x_4284_ = 122;
                    v___x_4285_ = lean_uint32_dec_le(v_c_4268_, v___x_4284_);
                    v___y_4276_ = v___x_4285_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_unquotedKeyFn___lam__0___boxed(
    mut v_c_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_4291_: u32 = 0;
    let mut v_res_4292_: u8 = 0;
    let mut v_r_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_4291_ = leanh::lean_unbox_uint32(v_c_4290_);
    leanh::lean_dec(v_c_4290_);
    v_res_4292_ = l_Lake_Toml_unquotedKeyFn___lam__0(v_c_boxed_4291_);
    v_r_4293_ = leanh::lean_box((v_res_4292_) as usize);
    return v_r_4293_;
}
pub unsafe fn l_Lake_Toml_unquotedKeyFn(
    mut v_a_4299_: *mut leanh::LeanObject,
    mut v_a_4300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4301_ = l_Lake_Toml_unquotedKeyFn___closed__0;
    v___x_4302_ = l_Lake_Toml_unquotedKeyFn___closed__2;
    v___x_4303_ = l_Lake_Toml_takeWhile1Fn(v___f_4301_, v___x_4302_, v_a_4299_, v_a_4300_);
    return v___x_4303_;
}
pub unsafe fn l_Lake_Toml_unquotedKeyFn___boxed(
    mut v_a_4304_: *mut leanh::LeanObject,
    mut v_a_4305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4306_ = l_Lake_Toml_unquotedKeyFn(v_a_4304_, v_a_4305_);
    leanh::lean_dec_ref(v_a_4304_);
    return v_res_4306_;
}
pub unsafe fn _init_l_Lake_Toml_unquotedKey___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4312_: u8 = 0;
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4312_ = 0;
    v___x_4313_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4314_ = leanh::lean_alloc_closure(
        l_Lake_Toml_unquotedKeyFn___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_4315_ = l_Lake_Toml_unquotedKey___closed__1;
    v___x_4316_ = l_Lake_Toml_unquotedKey___closed__0;
    v___x_4317_ = l_Lake_Toml_litWithAntiquot(
        v___x_4316_,
        v___x_4315_,
        v___x_4314_,
        v___x_4313_,
        v___x_4312_,
    );
    return v___x_4317_;
}
pub unsafe fn _init_l_Lake_Toml_unquotedKey() -> *mut leanh::LeanObject {
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_unquotedKey___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_unquotedKey___closed__2_once),
        _init_l_Lake_Toml_unquotedKey___closed__2,
    );
    return v___x_4318_;
}
pub unsafe fn _init_l_Lake_Toml_basicString___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4324_ = 0;
    v___x_4325_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4326_ =
        leanh::lean_alloc_closure(l_Lake_Toml_basicStringFn as *mut core::ffi::c_void, 2, 0);
    v___x_4327_ = l_Lake_Toml_basicString___closed__1;
    v___x_4328_ = l_Lake_Toml_basicString___closed__0;
    v___x_4329_ = l_Lake_Toml_litWithAntiquot(
        v___x_4328_,
        v___x_4327_,
        v___x_4326_,
        v___x_4325_,
        v___x_4324_,
    );
    return v___x_4329_;
}
pub unsafe fn _init_l_Lake_Toml_basicString() -> *mut leanh::LeanObject {
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4330_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_basicString___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_basicString___closed__2_once),
        _init_l_Lake_Toml_basicString___closed__2,
    );
    return v___x_4330_;
}
pub unsafe fn _init_l_Lake_Toml_literalString___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4336_: u8 = 0;
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4336_ = 0;
    v___x_4337_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4338_ = leanh::lean_alloc_closure(
        l_Lake_Toml_literalStringFn___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_4339_ = l_Lake_Toml_literalString___closed__1;
    v___x_4340_ = l_Lake_Toml_literalString___closed__0;
    v___x_4341_ = l_Lake_Toml_litWithAntiquot(
        v___x_4340_,
        v___x_4339_,
        v___x_4338_,
        v___x_4337_,
        v___x_4336_,
    );
    return v___x_4341_;
}
pub unsafe fn _init_l_Lake_Toml_literalString() -> *mut leanh::LeanObject {
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_literalString___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_literalString___closed__2_once),
        _init_l_Lake_Toml_literalString___closed__2,
    );
    return v___x_4342_;
}
pub unsafe fn _init_l_Lake_Toml_mlBasicString___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4348_: u8 = 0;
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = 0;
    v___x_4349_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4350_ = leanh::lean_alloc_closure(
        l_Lake_Toml_mlBasicStringFn as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_4351_ = l_Lake_Toml_mlBasicString___closed__1;
    v___x_4352_ = l_Lake_Toml_mlBasicString___closed__0;
    v___x_4353_ = l_Lake_Toml_litWithAntiquot(
        v___x_4352_,
        v___x_4351_,
        v___x_4350_,
        v___x_4349_,
        v___x_4348_,
    );
    return v___x_4353_;
}
pub unsafe fn _init_l_Lake_Toml_mlBasicString() -> *mut leanh::LeanObject {
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4354_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_mlBasicString___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_mlBasicString___closed__2_once),
        _init_l_Lake_Toml_mlBasicString___closed__2,
    );
    return v___x_4354_;
}
pub unsafe fn _init_l_Lake_Toml_mlLiteralString___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4360_ = 0;
    v___x_4361_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4362_ = leanh::lean_alloc_closure(
        l_Lake_Toml_mlLiteralStringFn as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_4363_ = l_Lake_Toml_mlLiteralString___closed__1;
    v___x_4364_ = l_Lake_Toml_mlLiteralString___closed__0;
    v___x_4365_ = l_Lake_Toml_litWithAntiquot(
        v___x_4364_,
        v___x_4363_,
        v___x_4362_,
        v___x_4361_,
        v___x_4360_,
    );
    return v___x_4365_;
}
pub unsafe fn _init_l_Lake_Toml_mlLiteralString() -> *mut leanh::LeanObject {
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4366_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_mlLiteralString___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_mlLiteralString___closed__2_once),
        _init_l_Lake_Toml_mlLiteralString___closed__2,
    );
    return v___x_4366_;
}
pub unsafe fn _init_l_Lake_Toml_quotedKey___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4367_ = l_Lake_Toml_literalString;
    v___x_4368_ = l_Lake_Toml_basicString;
    v___x_4369_ = l_Lean_Parser_orelse(v___x_4368_, v___x_4367_);
    return v___x_4369_;
}
pub unsafe fn _init_l_Lake_Toml_quotedKey() -> *mut leanh::LeanObject {
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_quotedKey___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_quotedKey___closed__0_once),
        _init_l_Lake_Toml_quotedKey___closed__0,
    );
    return v___x_4370_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4376_ = l_Lake_Toml_quotedKey;
    v___x_4377_ = l_Lake_Toml_unquotedKey;
    v___x_4378_ = l_Lean_Parser_orelse(v___x_4377_, v___x_4376_);
    return v___x_4378_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4379_ = 1;
    v___x_4380_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey___closed__2_once),
        _init_l_Lake_Toml_simpleKey___closed__2,
    );
    v___x_4381_ = l_Lake_Toml_simpleKey___closed__1;
    v___x_4382_ = l_Lake_Toml_simpleKey___closed__0;
    v___x_4383_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4382_, v___x_4381_, v___x_4380_, v___x_4379_);
    return v___x_4383_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey() -> *mut leanh::LeanObject {
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4384_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey___closed__3_once),
        _init_l_Lake_Toml_simpleKey___closed__3,
    );
    return v___x_4384_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4394_: u32 = 0;
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4394_ = 46;
    v___x_4395_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4396_ = lean_string_push(v___x_4395_, v___x_4394_);
    return v___x_4396_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__4_once),
        _init_l_Lake_Toml_key___closed__4,
    );
    v___x_4398_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4399_ = lean_string_append(v___x_4398_, v___x_4397_);
    return v___x_4399_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4400_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__5_once),
        _init_l_Lake_Toml_key___closed__5,
    );
    v___x_4402_ = lean_string_append(v___x_4401_, v___x_4400_);
    return v___x_4402_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4403_ = leanh::lean_box(0);
    v___x_4404_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__6_once),
        _init_l_Lake_Toml_key___closed__6,
    );
    v___x_4405_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4405_, 0, v___x_4404_);
    leanh::lean_ctor_set(v___x_4405_, 1, v___x_4403_);
    return v___x_4405_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u32 = 0;
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4406_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4407_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7_once),
        _init_l_Lake_Toml_key___closed__7,
    );
    v___x_4408_ = 46;
    v___x_4409_ = l_Lake_Toml_chAtom(v___x_4408_, v___x_4407_, v___x_4406_);
    return v___x_4409_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4410_ = l_Lake_Toml_trailingWs;
    v___x_4411_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__8_once),
        _init_l_Lake_Toml_key___closed__8,
    );
    v___x_4412_ = l_Lean_Parser_andthen(v___x_4411_, v___x_4410_);
    return v___x_4412_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__9_once),
        _init_l_Lake_Toml_key___closed__9,
    );
    v___x_4414_ = l_Lake_Toml_trailingWs;
    v___x_4415_ = l_Lean_Parser_andthen(v___x_4414_, v___x_4413_);
    return v___x_4415_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_4416_: u8 = 0;
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4416_ = 0;
    v___x_4417_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__10),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__10_once),
        _init_l_Lake_Toml_key___closed__10,
    );
    v___x_4418_ = l_Lake_Toml_key___closed__3;
    v___x_4419_ = l_Lake_Toml_simpleKey;
    v___x_4420_ = l_Lean_Parser_sepBy1(v___x_4419_, v___x_4418_, v___x_4417_, v___x_4416_);
    return v___x_4420_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4421_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__11),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__11_once),
        _init_l_Lake_Toml_key___closed__11,
    );
    v___x_4422_ = l_Lake_Toml_key___closed__2;
    v___x_4423_ = l_Lean_Parser_setExpected(v___x_4422_, v___x_4421_);
    return v___x_4423_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_4424_: u8 = 0;
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4424_ = 1;
    v___x_4425_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__12),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__12_once),
        _init_l_Lake_Toml_key___closed__12,
    );
    v___x_4426_ = l_Lake_Toml_key___closed__1;
    v___x_4427_ = l_Lake_Toml_key___closed__0;
    v___x_4428_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4427_, v___x_4426_, v___x_4425_, v___x_4424_);
    return v___x_4428_;
}
pub unsafe fn _init_l_Lake_Toml_key() -> *mut leanh::LeanObject {
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4429_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__13),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__13_once),
        _init_l_Lake_Toml_key___closed__13,
    );
    return v___x_4429_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: u32 = 0;
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4439_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4440_ = l_Lake_Toml_stdTable___closed__3;
    v___x_4441_ = 91;
    v___x_4442_ = l_Lake_Toml_chAtom(v___x_4441_, v___x_4440_, v___x_4439_);
    return v___x_4442_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4443_: u32 = 0;
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4443_ = 91;
    v___x_4444_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4445_ = lean_string_push(v___x_4444_, v___x_4443_);
    return v___x_4445_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4446_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__5_once),
        _init_l_Lake_Toml_stdTable___closed__5,
    );
    v___x_4447_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4448_ = lean_string_append(v___x_4447_, v___x_4446_);
    return v___x_4448_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4449_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4450_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__6_once),
        _init_l_Lake_Toml_stdTable___closed__6,
    );
    v___x_4451_ = lean_string_append(v___x_4450_, v___x_4449_);
    return v___x_4451_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4452_ = leanh::lean_box(0);
    v___x_4453_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__7_once),
        _init_l_Lake_Toml_stdTable___closed__7,
    );
    v___x_4454_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4454_, 0, v___x_4453_);
    leanh::lean_ctor_set(v___x_4454_, 1, v___x_4452_);
    return v___x_4454_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: u32 = 0;
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4456_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8_once),
        _init_l_Lake_Toml_stdTable___closed__8,
    );
    v___x_4457_ = 91;
    v___x_4458_ = l_Lake_Toml_chAtom(v___x_4457_, v___x_4456_, v___x_4455_);
    return v___x_4458_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lake_Toml_stdTable___closed__10;
    v___x_4461_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__9_once),
        _init_l_Lake_Toml_stdTable___closed__9,
    );
    v___x_4462_ = l_Lean_Parser_notFollowedBy(v___x_4461_, v___x_4460_);
    return v___x_4462_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4463_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__11),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__11_once),
        _init_l_Lake_Toml_stdTable___closed__11,
    );
    v___x_4464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__4_once),
        _init_l_Lake_Toml_stdTable___closed__4,
    );
    v___x_4465_ = l_Lean_Parser_andthen(v___x_4464_, v___x_4463_);
    return v___x_4465_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4466_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__12),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__12_once),
        _init_l_Lake_Toml_stdTable___closed__12,
    );
    v___x_4467_ = l_Lean_Parser_atomic(v___x_4466_);
    return v___x_4467_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_4468_: u32 = 0;
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4468_ = 93;
    v___x_4469_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4470_ = lean_string_push(v___x_4469_, v___x_4468_);
    return v___x_4470_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4471_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__14),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__14_once),
        _init_l_Lake_Toml_stdTable___closed__14,
    );
    v___x_4472_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4473_ = lean_string_append(v___x_4472_, v___x_4471_);
    return v___x_4473_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4475_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__15),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__15_once),
        _init_l_Lake_Toml_stdTable___closed__15,
    );
    v___x_4476_ = lean_string_append(v___x_4475_, v___x_4474_);
    return v___x_4476_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4477_ = leanh::lean_box(0);
    v___x_4478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__16),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__16_once),
        _init_l_Lake_Toml_stdTable___closed__16,
    );
    v___x_4479_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4479_, 0, v___x_4478_);
    leanh::lean_ctor_set(v___x_4479_, 1, v___x_4477_);
    return v___x_4479_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: u32 = 0;
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4480_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17_once),
        _init_l_Lake_Toml_stdTable___closed__17,
    );
    v___x_4482_ = 93;
    v___x_4483_ = l_Lake_Toml_chAtom(v___x_4482_, v___x_4481_, v___x_4480_);
    return v___x_4483_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18_once),
        _init_l_Lake_Toml_stdTable___closed__18,
    );
    v___x_4485_ = l_Lake_Toml_trailingWs;
    v___x_4486_ = l_Lean_Parser_andthen(v___x_4485_, v___x_4484_);
    return v___x_4486_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4487_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__19),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__19_once),
        _init_l_Lake_Toml_stdTable___closed__19,
    );
    v___x_4488_ = l_Lake_Toml_key;
    v___x_4489_ = l_Lean_Parser_andthen(v___x_4488_, v___x_4487_);
    return v___x_4489_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__20),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__20_once),
        _init_l_Lake_Toml_stdTable___closed__20,
    );
    v___x_4491_ = l_Lake_Toml_trailingWs;
    v___x_4492_ = l_Lean_Parser_andthen(v___x_4491_, v___x_4490_);
    return v___x_4492_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4493_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__21),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__21_once),
        _init_l_Lake_Toml_stdTable___closed__21,
    );
    v___x_4494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__13),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__13_once),
        _init_l_Lake_Toml_stdTable___closed__13,
    );
    v___x_4495_ = l_Lean_Parser_andthen(v___x_4494_, v___x_4493_);
    return v___x_4495_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4496_ = 0;
    v___x_4497_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__22),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__22_once),
        _init_l_Lake_Toml_stdTable___closed__22,
    );
    v___x_4498_ = l_Lake_Toml_stdTable___closed__1;
    v___x_4499_ = l_Lake_Toml_stdTable___closed__0;
    v___x_4500_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4499_, v___x_4498_, v___x_4497_, v___x_4496_);
    return v___x_4500_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable() -> *mut leanh::LeanObject {
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4501_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__23),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__23_once),
        _init_l_Lake_Toml_stdTable___closed__23,
    );
    return v___x_4501_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4507_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__9_once),
        _init_l_Lake_Toml_stdTable___closed__9,
    );
    v___x_4508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__4_once),
        _init_l_Lake_Toml_stdTable___closed__4,
    );
    v___x_4509_ = l_Lean_Parser_andthen(v___x_4508_, v___x_4507_);
    return v___x_4509_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4510_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__2_once),
        _init_l_Lake_Toml_arrayTable___closed__2,
    );
    v___x_4511_ = l_Lean_Parser_atomic(v___x_4510_);
    return v___x_4511_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4512_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18_once),
        _init_l_Lake_Toml_stdTable___closed__18,
    );
    v___x_4513_ = l_Lean_Parser_andthen(v___x_4512_, v___x_4512_);
    return v___x_4513_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4514_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__4_once),
        _init_l_Lake_Toml_arrayTable___closed__4,
    );
    v___x_4515_ = l_Lake_Toml_trailingWs;
    v___x_4516_ = l_Lean_Parser_andthen(v___x_4515_, v___x_4514_);
    return v___x_4516_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4517_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__5_once),
        _init_l_Lake_Toml_arrayTable___closed__5,
    );
    v___x_4518_ = l_Lake_Toml_key;
    v___x_4519_ = l_Lean_Parser_andthen(v___x_4518_, v___x_4517_);
    return v___x_4519_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4520_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__6_once),
        _init_l_Lake_Toml_arrayTable___closed__6,
    );
    v___x_4521_ = l_Lake_Toml_trailingWs;
    v___x_4522_ = l_Lean_Parser_andthen(v___x_4521_, v___x_4520_);
    return v___x_4522_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4523_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__7_once),
        _init_l_Lake_Toml_arrayTable___closed__7,
    );
    v___x_4524_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__3_once),
        _init_l_Lake_Toml_arrayTable___closed__3,
    );
    v___x_4525_ = l_Lean_Parser_andthen(v___x_4524_, v___x_4523_);
    return v___x_4525_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_4526_: u8 = 0;
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = 0;
    v___x_4527_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__8_once),
        _init_l_Lake_Toml_arrayTable___closed__8,
    );
    v___x_4528_ = l_Lake_Toml_arrayTable___closed__1;
    v___x_4529_ = l_Lake_Toml_arrayTable___closed__0;
    v___x_4530_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4529_, v___x_4528_, v___x_4527_, v___x_4526_);
    return v___x_4530_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable() -> *mut leanh::LeanObject {
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__9_once),
        _init_l_Lake_Toml_arrayTable___closed__9,
    );
    return v___x_4531_;
}
pub unsafe fn _init_l_Lake_Toml_table___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4532_ = l_Lake_Toml_arrayTable;
    v___x_4533_ = l_Lake_Toml_stdTable;
    v___x_4534_ = l_Lean_Parser_orelse(v___x_4533_, v___x_4532_);
    return v___x_4534_;
}
pub unsafe fn _init_l_Lake_Toml_table() -> *mut leanh::LeanObject {
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_table___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_table___closed__0_once),
        _init_l_Lake_Toml_table___closed__0,
    );
    return v___x_4535_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4541_: u32 = 0;
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4541_ = 61;
    v___x_4542_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4543_ = lean_string_push(v___x_4542_, v___x_4541_);
    return v___x_4543_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4544_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2,
    );
    v___x_4545_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4546_ = lean_string_append(v___x_4545_, v___x_4544_);
    return v___x_4546_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4547_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4548_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3,
    );
    v___x_4549_ = lean_string_append(v___x_4548_, v___x_4547_);
    return v___x_4549_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4550_ = leanh::lean_box(0);
    v___x_4551_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4,
    );
    v___x_4552_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4552_, 0, v___x_4551_);
    leanh::lean_ctor_set(v___x_4552_, 1, v___x_4550_);
    return v___x_4552_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: u32 = 0;
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4554_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5,
    );
    v___x_4555_ = 61;
    v___x_4556_ = l_Lake_Toml_chAtom(v___x_4555_, v___x_4554_, v___x_4553_);
    return v___x_4556_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(
    mut v_val_4557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
    v___x_4559_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
    v___x_4560_ = l_Lake_Toml_key;
    v___x_4561_ = l_Lake_Toml_trailingWs;
    v___x_4562_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6,
    );
    v___x_4563_ = l_Lean_Parser_andthen(v___x_4561_, v_val_4557_);
    v___x_4564_ = l_Lean_Parser_andthen(v___x_4562_, v___x_4563_);
    v___x_4565_ = l_Lean_Parser_andthen(v___x_4561_, v___x_4564_);
    v___x_4566_ = l_Lean_Parser_andthen(v___x_4560_, v___x_4565_);
    v___x_4567_ = 1;
    v___x_4568_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4558_, v___x_4559_, v___x_4566_, v___x_4567_);
    return v___x_4568_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4574_ = 1;
    v___x_4575_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1;
    v___x_4576_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0;
    v___x_4577_ = l_Lean_Parser_mkAntiquot(v___x_4576_, v___x_4575_, v___x_4574_, v___x_4574_);
    return v___x_4577_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(
    mut v_val_4578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4579_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2,
    );
    v___x_4580_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_4578_);
    v___x_4581_ = l_Lake_Toml_table;
    v___x_4582_ = l_Lean_Parser_orelse(v___x_4580_, v___x_4581_);
    v___x_4583_ = l_Lean_Parser_withAntiquot(v___x_4579_, v___x_4582_);
    return v___x_4583_;
}
pub unsafe fn _init_l_Lake_Toml_header___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4589_: u8 = 0;
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4589_ = 0;
    v___x_4590_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4591_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4592_ = l_Lake_Toml_header___closed__1;
    v___x_4593_ = l_Lake_Toml_header___closed__0;
    v___x_4594_ = l_Lake_Toml_litWithAntiquot(
        v___x_4593_,
        v___x_4592_,
        v___x_4591_,
        v___x_4590_,
        v___x_4589_,
    );
    return v___x_4594_;
}
pub unsafe fn _init_l_Lake_Toml_header() -> *mut leanh::LeanObject {
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4595_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_header___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_header___closed__2_once),
        _init_l_Lake_Toml_header___closed__2,
    );
    return v___x_4595_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4605_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4;
    v___x_4606_ = l_Lean_Parser_symbol(v___x_4605_);
    return v___x_4606_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4608_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6;
    v___x_4609_ = l_Lean_Parser_checkLinebreakBefore(v___x_4608_);
    return v___x_4609_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4610_ = l_Lean_Parser_pushNone;
    v___x_4611_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7,
    );
    v___x_4612_ = l_Lean_Parser_andthen(v___x_4611_, v___x_4610_);
    return v___x_4612_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(
    mut v_val_4613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: u8 = 0;
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4614_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
    v___x_4615_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
    v___x_4616_ = l_Lake_Toml_header;
    v___x_4617_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v_val_4613_);
    v___x_4618_ = l_Lake_Toml_trailingSep;
    v___x_4619_ = l_Lean_Parser_andthen(v___x_4617_, v___x_4618_);
    v___x_4620_ = 1;
    v___x_4621_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3;
    v___x_4622_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5,
    );
    v_p_4623_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_4621_, v___x_4619_, v___x_4622_);
    v___x_4624_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8,
    );
    v___x_4625_ = l_Lean_Parser_sepByNoAntiquot(v_p_4623_, v___x_4624_, v___x_4620_);
    v___x_4626_ = l_Lean_Parser_andthen(v___x_4616_, v___x_4625_);
    v___x_4627_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4614_, v___x_4615_, v___x_4626_, v___x_4620_);
    return v___x_4627_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: u32 = 0;
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4638_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3;
    v___x_4639_ = 123;
    v___x_4640_ = l_Lake_Toml_chAtom(v___x_4639_, v___x_4638_, v___x_4637_);
    return v___x_4640_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4642_: u32 = 0;
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4642_ = 44;
    v___x_4643_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4644_ = lean_string_push(v___x_4643_, v___x_4642_);
    return v___x_4644_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4645_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6,
    );
    v___x_4646_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4647_ = lean_string_append(v___x_4646_, v___x_4645_);
    return v___x_4647_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4648_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4649_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7,
    );
    v___x_4650_ = lean_string_append(v___x_4649_, v___x_4648_);
    return v___x_4650_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4651_ = leanh::lean_box(0);
    v___x_4652_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8,
    );
    v___x_4653_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4653_, 0, v___x_4652_);
    leanh::lean_ctor_set(v___x_4653_, 1, v___x_4651_);
    return v___x_4653_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u32 = 0;
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4654_ =
        leanh::lean_alloc_closure(l_Lake_Toml_wsFn___boxed as *mut core::ffi::c_void, 2, 0);
    v___x_4655_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9,
    );
    v___x_4656_ = 44;
    v___x_4657_ = l_Lake_Toml_chAtom(v___x_4656_, v___x_4655_, v___x_4654_);
    return v___x_4657_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4658_: u32 = 0;
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4658_ = 125;
    v___x_4659_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4660_ = lean_string_push(v___x_4659_, v___x_4658_);
    return v___x_4660_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11,
    );
    v___x_4662_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4663_ = lean_string_append(v___x_4662_, v___x_4661_);
    return v___x_4663_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4664_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4665_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12,
    );
    v___x_4666_ = lean_string_append(v___x_4665_, v___x_4664_);
    return v___x_4666_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4667_ = leanh::lean_box(0);
    v___x_4668_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13,
    );
    v___x_4669_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4669_, 0, v___x_4668_);
    leanh::lean_ctor_set(v___x_4669_, 1, v___x_4667_);
    return v___x_4669_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: u32 = 0;
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4670_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4671_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14,
    );
    v___x_4672_ = 125;
    v___x_4673_ = l_Lake_Toml_chAtom(v___x_4672_, v___x_4671_, v___x_4670_);
    return v___x_4673_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(
    mut v_val_4674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: u8 = 0;
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4675_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0;
    v___x_4676_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1;
    v___x_4677_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4,
    );
    v___x_4678_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_4674_);
    v___x_4679_ = l_Lake_Toml_trailingWs;
    v___x_4680_ = l_Lean_Parser_andthen(v___x_4678_, v___x_4679_);
    v___x_4681_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5;
    v___x_4682_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10,
    );
    v___x_4683_ = 0;
    v___x_4684_ = l_Lean_Parser_sepBy(v___x_4680_, v___x_4681_, v___x_4682_, v___x_4683_);
    v___x_4685_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15,
    );
    v___x_4686_ = l_Lean_Parser_andthen(v___x_4684_, v___x_4685_);
    v___x_4687_ = l_Lean_Parser_andthen(v___x_4677_, v___x_4686_);
    v___x_4688_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4675_, v___x_4676_, v___x_4687_, v___x_4683_);
    return v___x_4688_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: u32 = 0;
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4697_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4698_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2;
    v___x_4699_ = 91;
    v___x_4700_ = l_Lake_Toml_chAtom(v___x_4699_, v___x_4698_, v___x_4697_);
    return v___x_4700_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: u32 = 0;
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4701_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4702_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9,
    );
    v___x_4703_ = 44;
    v___x_4704_ = l_Lake_Toml_chAtom(v___x_4703_, v___x_4702_, v___x_4701_);
    return v___x_4704_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(
    mut v_val_4705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: u8 = 0;
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4706_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0;
    v___x_4707_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1;
    v___x_4708_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3,
    );
    v___x_4709_ = l_Lake_Toml_trailingSep;
    v___x_4710_ = l_Lean_Parser_andthen(v_val_4705_, v___x_4709_);
    v___x_4711_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5;
    v___x_4712_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4,
    );
    v___x_4713_ = 1;
    v___x_4714_ = l_Lean_Parser_sepBy(v___x_4710_, v___x_4711_, v___x_4712_, v___x_4713_);
    v___x_4715_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18_once),
        _init_l_Lake_Toml_stdTable___closed__18,
    );
    v___x_4716_ = l_Lean_Parser_andthen(v___x_4714_, v___x_4715_);
    v___x_4717_ = l_Lean_Parser_andthen(v___x_4708_, v___x_4716_);
    v___x_4718_ = 0;
    v___x_4719_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4706_, v___x_4707_, v___x_4717_, v___x_4718_);
    return v___x_4719_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4728_ = l_Lake_Toml_literalString;
    v___x_4729_ = l_Lake_Toml_mlLiteralString;
    v___x_4730_ = l_Lean_Parser_orelse(v___x_4729_, v___x_4728_);
    return v___x_4730_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4731_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__3_once),
        _init_l_Lake_Toml_string___closed__3,
    );
    v___x_4732_ = l_Lake_Toml_basicString;
    v___x_4733_ = l_Lean_Parser_orelse(v___x_4732_, v___x_4731_);
    return v___x_4733_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4734_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__4_once),
        _init_l_Lake_Toml_string___closed__4,
    );
    v___x_4735_ = l_Lake_Toml_mlBasicString;
    v___x_4736_ = l_Lean_Parser_orelse(v___x_4735_, v___x_4734_);
    return v___x_4736_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4737_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__5_once),
        _init_l_Lake_Toml_string___closed__5,
    );
    v___x_4738_ = l_Lake_Toml_string___closed__2;
    v___x_4739_ = l_Lean_Parser_setExpected(v___x_4738_, v___x_4737_);
    return v___x_4739_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_4740_: u8 = 0;
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4740_ = 0;
    v___x_4741_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__6_once),
        _init_l_Lake_Toml_string___closed__6,
    );
    v___x_4742_ = l_Lake_Toml_string___closed__1;
    v___x_4743_ = l_Lake_Toml_string___closed__0;
    v___x_4744_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4743_, v___x_4742_, v___x_4741_, v___x_4740_);
    return v___x_4744_;
}
pub unsafe fn _init_l_Lake_Toml_string() -> *mut leanh::LeanObject {
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4745_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__7_once),
        _init_l_Lake_Toml_string___closed__7,
    );
    return v___x_4745_;
}
pub unsafe fn _init_l_Lake_Toml_true___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4758_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4759_ = l_Lake_Toml_true___closed__4;
    v___x_4760_ = l_Lake_Toml_true___closed__1;
    v___x_4761_ = l_Lake_Toml_lit(v___x_4760_, v___x_4759_, v___x_4758_);
    return v___x_4761_;
}
pub unsafe fn _init_l_Lake_Toml_true() -> *mut leanh::LeanObject {
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4762_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_true___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_true___closed__5_once),
        _init_l_Lake_Toml_true___closed__5,
    );
    return v___x_4762_;
}
pub unsafe fn _init_l_Lake_Toml_false___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4775_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4776_ = l_Lake_Toml_false___closed__4;
    v___x_4777_ = l_Lake_Toml_false___closed__1;
    v___x_4778_ = l_Lake_Toml_lit(v___x_4777_, v___x_4776_, v___x_4775_);
    return v___x_4778_;
}
pub unsafe fn _init_l_Lake_Toml_false() -> *mut leanh::LeanObject {
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4779_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_false___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_false___closed__5_once),
        _init_l_Lake_Toml_false___closed__5,
    );
    return v___x_4779_;
}
pub unsafe fn _init_l_Lake_Toml_boolean___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4785_ = l_Lake_Toml_false;
    v___x_4786_ = l_Lake_Toml_true;
    v___x_4787_ = l_Lean_Parser_orelse(v___x_4786_, v___x_4785_);
    return v___x_4787_;
}
pub unsafe fn _init_l_Lake_Toml_boolean___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4788_: u8 = 0;
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4788_ = 0;
    v___x_4789_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_boolean___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_boolean___closed__2_once),
        _init_l_Lake_Toml_boolean___closed__2,
    );
    v___x_4790_ = l_Lake_Toml_boolean___closed__1;
    v___x_4791_ = l_Lake_Toml_boolean___closed__0;
    v___x_4792_ =
        l_Lean_Parser_nodeWithAntiquot(v___x_4791_, v___x_4790_, v___x_4789_, v___x_4788_);
    return v___x_4792_;
}
pub unsafe fn _init_l_Lake_Toml_boolean() -> *mut leanh::LeanObject {
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4793_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_boolean___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_boolean___closed__3_once),
        _init_l_Lake_Toml_boolean___closed__3,
    );
    return v___x_4793_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4794_ = 0;
    v___x_4795_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
    v___x_4796_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
    v___x_4797_ = l_Lean_Parser_mkAntiquot(v___x_4796_, v___x_4795_, v___x_4794_, v___x_4794_);
    return v___x_4797_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4798_: u8 = 0;
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4798_ = 0;
    v___x_4799_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
    v___x_4800_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5;
    v___x_4801_ = l_Lean_Parser_mkAntiquot(v___x_4800_, v___x_4799_, v___x_4798_, v___x_4798_);
    return v___x_4801_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4802_: u8 = 0;
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4802_ = 0;
    v___x_4803_ = l_Lake_Toml_numeralFn___lam__0___closed__17;
    v___x_4804_ = l_Lake_Toml_numeralFn___lam__0___closed__16;
    v___x_4805_ = l_Lean_Parser_mkAntiquot(v___x_4804_, v___x_4803_, v___x_4802_, v___x_4802_);
    return v___x_4805_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4806_: u8 = 0;
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4806_ = 0;
    v___x_4807_ = l_Lake_Toml_numeralFn___lam__0___closed__12;
    v___x_4808_ = l_Lake_Toml_numeralFn___lam__0___closed__11;
    v___x_4809_ = l_Lean_Parser_mkAntiquot(v___x_4808_, v___x_4807_, v___x_4806_, v___x_4806_);
    return v___x_4809_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4810_: u8 = 0;
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4810_ = 0;
    v___x_4811_ = l_Lake_Toml_numeralFn___lam__0___closed__7;
    v___x_4812_ = l_Lake_Toml_numeralFn___lam__0___closed__6;
    v___x_4813_ = l_Lean_Parser_mkAntiquot(v___x_4812_, v___x_4811_, v___x_4810_, v___x_4810_);
    return v___x_4813_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4814_: u8 = 0;
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4814_ = 0;
    v___x_4815_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
    v___x_4816_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0;
    v___x_4817_ = l_Lean_Parser_mkAntiquot(v___x_4816_, v___x_4815_, v___x_4814_, v___x_4814_);
    return v___x_4817_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_4823_: u8 = 0;
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4823_ = 1;
    v___x_4824_ = l_Lake_Toml_numeralAntiquot___closed__7;
    v___x_4825_ = l_Lake_Toml_numeralAntiquot___closed__6;
    v___x_4826_ = l_Lean_Parser_mkAntiquot(v___x_4825_, v___x_4824_, v___x_4823_, v___x_4823_);
    return v___x_4826_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4827_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__8_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__8,
    );
    v___x_4828_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__5_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__5,
    );
    v___x_4829_ = l_Lean_Parser_orelse(v___x_4828_, v___x_4827_);
    return v___x_4829_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4830_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__9_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__9,
    );
    v___x_4831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__4_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__4,
    );
    v___x_4832_ = l_Lean_Parser_orelse(v___x_4831_, v___x_4830_);
    return v___x_4832_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4833_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__10),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__10_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__10,
    );
    v___x_4834_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__3_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__3,
    );
    v___x_4835_ = l_Lean_Parser_orelse(v___x_4834_, v___x_4833_);
    return v___x_4835_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4836_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__11),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__11_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__11,
    );
    v___x_4837_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__2_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__2,
    );
    v___x_4838_ = l_Lean_Parser_orelse(v___x_4837_, v___x_4836_);
    return v___x_4838_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4839_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__12),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__12_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__12,
    );
    v___x_4840_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__1_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__1,
    );
    v___x_4841_ = l_Lean_Parser_orelse(v___x_4840_, v___x_4839_);
    return v___x_4841_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4842_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__13),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__13_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__13,
    );
    v___x_4843_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__0_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__0,
    );
    v___x_4844_ = l_Lean_Parser_orelse(v___x_4843_, v___x_4842_);
    return v___x_4844_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot() -> *mut leanh::LeanObject {
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4845_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__14),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__14_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__14,
    );
    return v___x_4845_;
}
pub unsafe fn _init_l_Lake_Toml_numeral___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4846_ =
        leanh::lean_alloc_closure(l_Lake_Toml_numeralFn as *mut core::ffi::c_void, 2, 0);
    v___x_4847_ = l_Lake_Toml_dynamicNode(v___x_4846_);
    return v___x_4847_;
}
pub unsafe fn _init_l_Lake_Toml_numeral___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4848_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeral___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeral___closed__0_once),
        _init_l_Lake_Toml_numeral___closed__0,
    );
    v___x_4849_ = l_Lake_Toml_numeralAntiquot;
    v___x_4850_ = l_Lean_Parser_withAntiquot(v___x_4849_, v___x_4848_);
    return v___x_4850_;
}
pub unsafe fn _init_l_Lake_Toml_numeral() -> *mut leanh::LeanObject {
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4851_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeral___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeral___closed__1_once),
        _init_l_Lake_Toml_numeral___closed__1,
    );
    return v___x_4851_;
}
pub unsafe fn l_Lake_Toml_numeralOfKind___lam__0(
    mut v_kind_4852_: *mut leanh::LeanObject,
    mut v_x_4853_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4854_: u8 = 0;
    v___x_4854_ = l_Lean_Syntax_isOfKind(v_x_4853_, v_kind_4852_);
    return v___x_4854_;
}
pub unsafe fn l_Lake_Toml_numeralOfKind___lam__0___boxed(
    mut v_kind_4855_: *mut leanh::LeanObject,
    mut v_x_4856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4857_: u8 = 0;
    let mut v_r_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4857_ = l_Lake_Toml_numeralOfKind___lam__0(v_kind_4855_, v_x_4856_);
    leanh::lean_dec(v_kind_4855_);
    v_r_4858_ = leanh::lean_box((v_res_4857_) as usize);
    return v_r_4858_;
}
pub unsafe fn l_Lake_Toml_numeralOfKind(
    mut v_name_4860_: *mut leanh::LeanObject,
    mut v_kind_4861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4862_ = leanh::lean_alloc_closure(
        l_Lake_Toml_numeralOfKind___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4862_, 0, v_kind_4861_);
    v___x_4863_ = l_Lake_Toml_numeral;
    v___x_4864_ = leanh::lean_box(0);
    v___x_4865_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4865_, 0, v_name_4860_);
    leanh::lean_ctor_set(v___x_4865_, 1, v___x_4864_);
    v___x_4866_ = l_Lake_Toml_numeralOfKind___closed__0;
    v___x_4867_ = l_Lean_Parser_checkStackTop(v___f_4862_, v___x_4866_);
    v___x_4868_ = l_Lean_Parser_setExpected(v___x_4865_, v___x_4867_);
    v___x_4869_ = l_Lean_Parser_andthen(v___x_4863_, v___x_4868_);
    return v___x_4869_;
}
pub unsafe fn _init_l_Lake_Toml_float___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4870_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
    v___x_4871_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
    v___x_4872_ = l_Lake_Toml_numeralOfKind(v___x_4871_, v___x_4870_);
    return v___x_4872_;
}
pub unsafe fn _init_l_Lake_Toml_float() -> *mut leanh::LeanObject {
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4873_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_float___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_float___closed__0_once),
        _init_l_Lake_Toml_float___closed__0,
    );
    return v___x_4873_;
}
pub unsafe fn _init_l_Lake_Toml_decInt___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4874_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
    v___x_4875_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0;
    v___x_4876_ = l_Lake_Toml_numeralOfKind(v___x_4875_, v___x_4874_);
    return v___x_4876_;
}
pub unsafe fn _init_l_Lake_Toml_decInt() -> *mut leanh::LeanObject {
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4877_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_decInt___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_decInt___closed__0_once),
        _init_l_Lake_Toml_decInt___closed__0,
    );
    return v___x_4877_;
}
pub unsafe fn _init_l_Lake_Toml_binNum___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4879_ = l_Lake_Toml_numeralFn___lam__0___closed__17;
    v___x_4880_ = l_Lake_Toml_binNum___closed__0;
    v___x_4881_ = l_Lake_Toml_numeralOfKind(v___x_4880_, v___x_4879_);
    return v___x_4881_;
}
pub unsafe fn _init_l_Lake_Toml_binNum() -> *mut leanh::LeanObject {
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4882_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_binNum___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_binNum___closed__1_once),
        _init_l_Lake_Toml_binNum___closed__1,
    );
    return v___x_4882_;
}
pub unsafe fn _init_l_Lake_Toml_octNum___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4884_ = l_Lake_Toml_numeralFn___lam__0___closed__12;
    v___x_4885_ = l_Lake_Toml_octNum___closed__0;
    v___x_4886_ = l_Lake_Toml_numeralOfKind(v___x_4885_, v___x_4884_);
    return v___x_4886_;
}
pub unsafe fn _init_l_Lake_Toml_octNum() -> *mut leanh::LeanObject {
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4887_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_octNum___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_octNum___closed__1_once),
        _init_l_Lake_Toml_octNum___closed__1,
    );
    return v___x_4887_;
}
pub unsafe fn _init_l_Lake_Toml_hexNum___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4889_ = l_Lake_Toml_numeralFn___lam__0___closed__7;
    v___x_4890_ = l_Lake_Toml_hexNum___closed__0;
    v___x_4891_ = l_Lake_Toml_numeralOfKind(v___x_4890_, v___x_4889_);
    return v___x_4891_;
}
pub unsafe fn _init_l_Lake_Toml_hexNum() -> *mut leanh::LeanObject {
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4892_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_hexNum___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_hexNum___closed__1_once),
        _init_l_Lake_Toml_hexNum___closed__1,
    );
    return v___x_4892_;
}
pub unsafe fn _init_l_Lake_Toml_dateTime___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4893_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
    v___x_4894_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2;
    v___x_4895_ = l_Lake_Toml_numeralOfKind(v___x_4894_, v___x_4893_);
    return v___x_4895_;
}
pub unsafe fn _init_l_Lake_Toml_dateTime() -> *mut leanh::LeanObject {
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4896_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_dateTime___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_dateTime___closed__0_once),
        _init_l_Lake_Toml_dateTime___closed__0,
    );
    return v___x_4896_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(
    mut v_val_4897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4898_ = l_Lake_Toml_string;
    v___x_4899_ = l_Lake_Toml_boolean;
    v___x_4900_ = l_Lake_Toml_numeral;
    leanh::lean_inc_ref(v_val_4897_);
    v___x_4901_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v_val_4897_);
    v___x_4902_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v_val_4897_);
    v___x_4903_ = l_Lean_Parser_orelse(v___x_4901_, v___x_4902_);
    v___x_4904_ = l_Lean_Parser_orelse(v___x_4900_, v___x_4903_);
    v___x_4905_ = l_Lean_Parser_orelse(v___x_4899_, v___x_4904_);
    v___x_4906_ = l_Lean_Parser_orelse(v___x_4898_, v___x_4905_);
    return v___x_4906_;
}
pub unsafe fn _init_l_Lake_Toml_val___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4913_: u8 = 0;
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4913_ = 1;
    v___x_4914_ = l_Lake_Toml_val___closed__2;
    v___x_4915_ = l_Lake_Toml_val___closed__1;
    v___x_4916_ = l_Lake_Toml_val___closed__0;
    v___x_4917_ =
        l_Lake_Toml_recNodeWithAntiquot(v___x_4916_, v___x_4915_, v___x_4914_, v___x_4913_);
    return v___x_4917_;
}
pub unsafe fn _init_l_Lake_Toml_val() -> *mut leanh::LeanObject {
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4918_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_val___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_val___closed__3_once),
        _init_l_Lake_Toml_val___closed__3,
    );
    return v___x_4918_;
}
pub unsafe fn _init_l_Lake_Toml_array___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4919_ = l_Lake_Toml_val;
    v___x_4920_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v___x_4919_);
    return v___x_4920_;
}
pub unsafe fn _init_l_Lake_Toml_array() -> *mut leanh::LeanObject {
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4921_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_array___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_array___closed__0_once),
        _init_l_Lake_Toml_array___closed__0,
    );
    return v___x_4921_;
}
pub unsafe fn _init_l_Lake_Toml_inlineTable___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4922_ = l_Lake_Toml_val;
    v___x_4923_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v___x_4922_);
    return v___x_4923_;
}
pub unsafe fn _init_l_Lake_Toml_inlineTable() -> *mut leanh::LeanObject {
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4924_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_inlineTable___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_inlineTable___closed__0_once),
        _init_l_Lake_Toml_inlineTable___closed__0,
    );
    return v___x_4924_;
}
pub unsafe fn _init_l_Lake_Toml_keyval___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4925_ = l_Lake_Toml_val;
    v___x_4926_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v___x_4925_);
    return v___x_4926_;
}
pub unsafe fn _init_l_Lake_Toml_keyval() -> *mut leanh::LeanObject {
    let mut v___x_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4927_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_keyval___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_keyval___closed__0_once),
        _init_l_Lake_Toml_keyval___closed__0,
    );
    return v___x_4927_;
}
pub unsafe fn _init_l_Lake_Toml_expression___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4928_ = l_Lake_Toml_val;
    v___x_4929_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v___x_4928_);
    return v___x_4929_;
}
pub unsafe fn _init_l_Lake_Toml_expression() -> *mut leanh::LeanObject {
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4930_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_expression___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_expression___closed__0_once),
        _init_l_Lake_Toml_expression___closed__0,
    );
    return v___x_4930_;
}
pub unsafe fn l_Lake_Toml_header_formatter(
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
    mut v_a_4934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: u8 = 0;
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4936_ = l_Lake_Toml_header___closed__0;
    v___x_4937_ = l_Lake_Toml_header___closed__1;
    v___x_4938_ = 0;
    v___x_4939_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(
        v___x_4936_,
        v___x_4937_,
        v___x_4938_,
        v_a_4931_,
        v_a_4932_,
        v_a_4933_,
        v_a_4934_,
    );
    return v___x_4939_;
}
pub unsafe fn l_Lake_Toml_header_formatter___boxed(
    mut v_a_4940_: *mut leanh::LeanObject,
    mut v_a_4941_: *mut leanh::LeanObject,
    mut v_a_4942_: *mut leanh::LeanObject,
    mut v_a_4943_: *mut leanh::LeanObject,
    mut v_a_4944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4945_ = l_Lake_Toml_header_formatter(v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
    leanh::lean_dec(v_a_4943_);
    leanh::lean_dec_ref(v_a_4942_);
    leanh::lean_dec(v_a_4941_);
    leanh::lean_dec_ref(v_a_4940_);
    return v_res_4945_;
}
pub unsafe fn l_Lake_Toml_unquotedKey_formatter(
    mut v_a_4946_: *mut leanh::LeanObject,
    mut v_a_4947_: *mut leanh::LeanObject,
    mut v_a_4948_: *mut leanh::LeanObject,
    mut v_a_4949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: u8 = 0;
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4951_ = l_Lake_Toml_unquotedKey___closed__0;
    v___x_4952_ = l_Lake_Toml_unquotedKey___closed__1;
    v___x_4953_ = 0;
    v___x_4954_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(
        v___x_4951_,
        v___x_4952_,
        v___x_4953_,
        v_a_4946_,
        v_a_4947_,
        v_a_4948_,
        v_a_4949_,
    );
    return v___x_4954_;
}
pub unsafe fn l_Lake_Toml_unquotedKey_formatter___boxed(
    mut v_a_4955_: *mut leanh::LeanObject,
    mut v_a_4956_: *mut leanh::LeanObject,
    mut v_a_4957_: *mut leanh::LeanObject,
    mut v_a_4958_: *mut leanh::LeanObject,
    mut v_a_4959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4960_ = l_Lake_Toml_unquotedKey_formatter(v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_);
    leanh::lean_dec(v_a_4958_);
    leanh::lean_dec_ref(v_a_4957_);
    leanh::lean_dec(v_a_4956_);
    leanh::lean_dec_ref(v_a_4955_);
    return v_res_4960_;
}
pub unsafe fn l_Lake_Toml_basicString_formatter(
    mut v_a_4961_: *mut leanh::LeanObject,
    mut v_a_4962_: *mut leanh::LeanObject,
    mut v_a_4963_: *mut leanh::LeanObject,
    mut v_a_4964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4966_ = l_Lake_Toml_basicString___closed__0;
    v___x_4967_ = l_Lake_Toml_basicString___closed__1;
    v___x_4968_ = 0;
    v___x_4969_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(
        v___x_4966_,
        v___x_4967_,
        v___x_4968_,
        v_a_4961_,
        v_a_4962_,
        v_a_4963_,
        v_a_4964_,
    );
    return v___x_4969_;
}
pub unsafe fn l_Lake_Toml_basicString_formatter___boxed(
    mut v_a_4970_: *mut leanh::LeanObject,
    mut v_a_4971_: *mut leanh::LeanObject,
    mut v_a_4972_: *mut leanh::LeanObject,
    mut v_a_4973_: *mut leanh::LeanObject,
    mut v_a_4974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4975_ = l_Lake_Toml_basicString_formatter(v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_);
    leanh::lean_dec(v_a_4973_);
    leanh::lean_dec_ref(v_a_4972_);
    leanh::lean_dec(v_a_4971_);
    leanh::lean_dec_ref(v_a_4970_);
    return v_res_4975_;
}
pub unsafe fn l_Lake_Toml_literalString_formatter(
    mut v_a_4976_: *mut leanh::LeanObject,
    mut v_a_4977_: *mut leanh::LeanObject,
    mut v_a_4978_: *mut leanh::LeanObject,
    mut v_a_4979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: u8 = 0;
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4981_ = l_Lake_Toml_literalString___closed__0;
    v___x_4982_ = l_Lake_Toml_literalString___closed__1;
    v___x_4983_ = 0;
    v___x_4984_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(
        v___x_4981_,
        v___x_4982_,
        v___x_4983_,
        v_a_4976_,
        v_a_4977_,
        v_a_4978_,
        v_a_4979_,
    );
    return v___x_4984_;
}
pub unsafe fn l_Lake_Toml_literalString_formatter___boxed(
    mut v_a_4985_: *mut leanh::LeanObject,
    mut v_a_4986_: *mut leanh::LeanObject,
    mut v_a_4987_: *mut leanh::LeanObject,
    mut v_a_4988_: *mut leanh::LeanObject,
    mut v_a_4989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4990_ = l_Lake_Toml_literalString_formatter(v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
    leanh::lean_dec(v_a_4988_);
    leanh::lean_dec_ref(v_a_4987_);
    leanh::lean_dec(v_a_4986_);
    leanh::lean_dec_ref(v_a_4985_);
    return v_res_4990_;
}
pub unsafe fn l_Lake_Toml_quotedKey_formatter(
    mut v_a_4991_: *mut leanh::LeanObject,
    mut v_a_4992_: *mut leanh::LeanObject,
    mut v_a_4993_: *mut leanh::LeanObject,
    mut v_a_4994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4996_ = leanh::lean_alloc_closure(
        l_Lake_Toml_basicString_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4997_ = leanh::lean_alloc_closure(
        l_Lake_Toml_literalString_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4998_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_4996_,
        v___x_4997_,
        v_a_4991_,
        v_a_4992_,
        v_a_4993_,
        v_a_4994_,
    );
    return v___x_4998_;
}
pub unsafe fn l_Lake_Toml_quotedKey_formatter___boxed(
    mut v_a_4999_: *mut leanh::LeanObject,
    mut v_a_5000_: *mut leanh::LeanObject,
    mut v_a_5001_: *mut leanh::LeanObject,
    mut v_a_5002_: *mut leanh::LeanObject,
    mut v_a_5003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5004_ = l_Lake_Toml_quotedKey_formatter(v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
    leanh::lean_dec(v_a_5002_);
    leanh::lean_dec_ref(v_a_5001_);
    leanh::lean_dec(v_a_5000_);
    leanh::lean_dec_ref(v_a_4999_);
    return v_res_5004_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey_formatter___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5005_ = leanh::lean_alloc_closure(
        l_Lake_Toml_quotedKey_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5006_ = leanh::lean_alloc_closure(
        l_Lake_Toml_unquotedKey_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5007_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5007_, 0, v___x_5006_);
    leanh::lean_closure_set(v___x_5007_, 1, v___x_5005_);
    return v___x_5007_;
}
pub unsafe fn l_Lake_Toml_simpleKey_formatter(
    mut v_a_5008_: *mut leanh::LeanObject,
    mut v_a_5009_: *mut leanh::LeanObject,
    mut v_a_5010_: *mut leanh::LeanObject,
    mut v_a_5011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5013_ = l_Lake_Toml_simpleKey___closed__0;
    v___x_5014_ = l_Lake_Toml_simpleKey___closed__1;
    v___x_5015_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey_formatter___closed__0_once),
        _init_l_Lake_Toml_simpleKey_formatter___closed__0,
    );
    v___x_5016_ = 1;
    v___x_5017_ = l_Lean_Parser_nodeWithAntiquot_formatter(
        v___x_5013_,
        v___x_5014_,
        v___x_5015_,
        v___x_5016_,
        v_a_5008_,
        v_a_5009_,
        v_a_5010_,
        v_a_5011_,
    );
    return v___x_5017_;
}
pub unsafe fn l_Lake_Toml_simpleKey_formatter___boxed(
    mut v_a_5018_: *mut leanh::LeanObject,
    mut v_a_5019_: *mut leanh::LeanObject,
    mut v_a_5020_: *mut leanh::LeanObject,
    mut v_a_5021_: *mut leanh::LeanObject,
    mut v_a_5022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5023_ = l_Lake_Toml_simpleKey_formatter(v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_);
    leanh::lean_dec(v_a_5021_);
    leanh::lean_dec_ref(v_a_5020_);
    leanh::lean_dec(v_a_5019_);
    leanh::lean_dec_ref(v_a_5018_);
    return v_res_5023_;
}
pub unsafe fn l_Lake_Toml_trailingWs_formatter___redArg() -> *mut leanh::LeanObject {
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_5025_;
}
pub unsafe fn l_Lake_Toml_trailingWs_formatter___redArg___boxed(
    mut v_a_5026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5027_ = l_Lake_Toml_trailingWs_formatter___redArg();
    return v_res_5027_;
}
pub unsafe fn l_Lake_Toml_trailingWs_formatter(
    mut v_a_5028_: *mut leanh::LeanObject,
    mut v_a_5029_: *mut leanh::LeanObject,
    mut v_a_5030_: *mut leanh::LeanObject,
    mut v_a_5031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_5033_;
}
pub unsafe fn l_Lake_Toml_trailingWs_formatter___boxed(
    mut v_a_5034_: *mut leanh::LeanObject,
    mut v_a_5035_: *mut leanh::LeanObject,
    mut v_a_5036_: *mut leanh::LeanObject,
    mut v_a_5037_: *mut leanh::LeanObject,
    mut v_a_5038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5039_ = l_Lake_Toml_trailingWs_formatter(v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
    leanh::lean_dec(v_a_5037_);
    leanh::lean_dec_ref(v_a_5036_);
    leanh::lean_dec(v_a_5035_);
    leanh::lean_dec_ref(v_a_5034_);
    return v_res_5039_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_5040_: u32 = 0;
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5040_ = 46;
    v___x_5041_ = leanh::lean_box_uint32(v___x_5040_);
    return v___x_5041_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5042_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5043_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7_once),
        _init_l_Lake_Toml_key___closed__7,
    );
    v___x_5044_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
    v___x_5045_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5045_, 0, v___x_5044_);
    leanh::lean_closure_set(v___x_5045_, 1, v___x_5043_);
    leanh::lean_closure_set(v___x_5045_, 2, v___x_5042_);
    return v___x_5045_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5046_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5047_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__0_once),
        _init_l_Lake_Toml_key_formatter___closed__0,
    );
    v___x_5048_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5048_, 0, v___x_5047_);
    leanh::lean_closure_set(v___x_5048_, 1, v___x_5046_);
    return v___x_5048_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5049_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__1_once),
        _init_l_Lake_Toml_key_formatter___closed__1,
    );
    v___x_5050_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5051_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5051_, 0, v___x_5050_);
    leanh::lean_closure_set(v___x_5051_, 1, v___x_5049_);
    return v___x_5051_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_5052_: u8 = 0;
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = 0;
    v___x_5053_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__2_once),
        _init_l_Lake_Toml_key_formatter___closed__2,
    );
    v___x_5054_ = l_Lake_Toml_key___closed__3;
    v___x_5055_ = leanh::lean_alloc_closure(
        l_Lake_Toml_simpleKey_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5056_ = leanh::lean_box((v___x_5052_) as usize);
    v___x_5057_ = leanh::lean_alloc_closure(
        l_Lean_Parser_sepBy1_formatter___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_5057_, 0, v___x_5055_);
    leanh::lean_closure_set(v___x_5057_, 1, v___x_5054_);
    leanh::lean_closure_set(v___x_5057_, 2, v___x_5053_);
    leanh::lean_closure_set(v___x_5057_, 3, v___x_5056_);
    return v___x_5057_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5058_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__3_once),
        _init_l_Lake_Toml_key_formatter___closed__3,
    );
    v___x_5059_ = l_Lake_Toml_key___closed__2;
    v___x_5060_ = leanh::lean_alloc_closure(
        l_Lean_Parser_setExpected_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5060_, 0, v___x_5059_);
    leanh::lean_closure_set(v___x_5060_, 1, v___x_5058_);
    return v___x_5060_;
}
pub unsafe fn l_Lake_Toml_key_formatter(
    mut v_a_5061_: *mut leanh::LeanObject,
    mut v_a_5062_: *mut leanh::LeanObject,
    mut v_a_5063_: *mut leanh::LeanObject,
    mut v_a_5064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: u8 = 0;
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5066_ = l_Lake_Toml_key___closed__0;
    v___x_5067_ = l_Lake_Toml_key___closed__1;
    v___x_5068_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__4_once),
        _init_l_Lake_Toml_key_formatter___closed__4,
    );
    v___x_5069_ = 1;
    v___x_5070_ = l_Lean_Parser_nodeWithAntiquot_formatter(
        v___x_5066_,
        v___x_5067_,
        v___x_5068_,
        v___x_5069_,
        v_a_5061_,
        v_a_5062_,
        v_a_5063_,
        v_a_5064_,
    );
    return v___x_5070_;
}
pub unsafe fn l_Lake_Toml_key_formatter___boxed(
    mut v_a_5071_: *mut leanh::LeanObject,
    mut v_a_5072_: *mut leanh::LeanObject,
    mut v_a_5073_: *mut leanh::LeanObject,
    mut v_a_5074_: *mut leanh::LeanObject,
    mut v_a_5075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5076_ = l_Lake_Toml_key_formatter(v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
    leanh::lean_dec(v_a_5074_);
    leanh::lean_dec_ref(v_a_5073_);
    leanh::lean_dec(v_a_5072_);
    leanh::lean_dec_ref(v_a_5071_);
    return v_res_5076_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_5077_: u32 = 0;
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5077_ = 61;
    v___x_5078_ = leanh::lean_box_uint32(v___x_5077_);
    return v___x_5078_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5079_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5080_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5,
    );
    v___x_5081_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
    v___x_5082_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5082_, 0, v___x_5081_);
    leanh::lean_closure_set(v___x_5082_, 1, v___x_5080_);
    leanh::lean_closure_set(v___x_5082_, 2, v___x_5079_);
    return v___x_5082_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(
    mut v_val_5083_: *mut leanh::LeanObject,
    mut v_a_5084_: *mut leanh::LeanObject,
    mut v_a_5085_: *mut leanh::LeanObject,
    mut v_a_5086_: *mut leanh::LeanObject,
    mut v_a_5087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: u8 = 0;
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5089_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
    v___x_5090_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
    v___x_5091_ = leanh::lean_alloc_closure(
        l_Lake_Toml_key_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5092_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5093_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0,
    );
    leanh::lean_inc_ref(v___x_5092_);
    v___x_5094_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5094_, 0, v___x_5092_);
    leanh::lean_closure_set(v___x_5094_, 1, v_val_5083_);
    v___x_5095_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5095_, 0, v___x_5093_);
    leanh::lean_closure_set(v___x_5095_, 1, v___x_5094_);
    v___x_5096_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5096_, 0, v___x_5092_);
    leanh::lean_closure_set(v___x_5096_, 1, v___x_5095_);
    v___x_5097_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5097_, 0, v___x_5091_);
    leanh::lean_closure_set(v___x_5097_, 1, v___x_5096_);
    v___x_5098_ = 1;
    v___x_5099_ = l_Lean_Parser_nodeWithAntiquot_formatter(
        v___x_5089_,
        v___x_5090_,
        v___x_5097_,
        v___x_5098_,
        v_a_5084_,
        v_a_5085_,
        v_a_5086_,
        v_a_5087_,
    );
    return v___x_5099_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed(
    mut v_val_5100_: *mut leanh::LeanObject,
    mut v_a_5101_: *mut leanh::LeanObject,
    mut v_a_5102_: *mut leanh::LeanObject,
    mut v_a_5103_: *mut leanh::LeanObject,
    mut v_a_5104_: *mut leanh::LeanObject,
    mut v_a_5105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5106_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(
        v_val_5100_,
        v_a_5101_,
        v_a_5102_,
        v_a_5103_,
        v_a_5104_,
    );
    leanh::lean_dec(v_a_5104_);
    leanh::lean_dec_ref(v_a_5103_);
    leanh::lean_dec(v_a_5102_);
    leanh::lean_dec_ref(v_a_5101_);
    return v_res_5106_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_5107_: u32 = 0;
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5107_ = 91;
    v___x_5108_ = leanh::lean_box_uint32(v___x_5107_);
    return v___x_5108_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5109_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5110_ = l_Lake_Toml_stdTable___closed__3;
    v___x_5111_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
    v___x_5112_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5112_, 0, v___x_5111_);
    leanh::lean_closure_set(v___x_5112_, 1, v___x_5110_);
    leanh::lean_closure_set(v___x_5112_, 2, v___x_5109_);
    return v___x_5112_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5113_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5114_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8_once),
        _init_l_Lake_Toml_stdTable___closed__8,
    );
    v___x_5115_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
    v___x_5116_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5116_, 0, v___x_5115_);
    leanh::lean_closure_set(v___x_5116_, 1, v___x_5114_);
    leanh::lean_closure_set(v___x_5116_, 2, v___x_5113_);
    return v___x_5116_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5117_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__1_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__1,
    );
    v___x_5118_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5118_, 0, v___x_5117_);
    return v___x_5118_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5119_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__2_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__2,
    );
    v___x_5120_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__0_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__0,
    );
    v___x_5121_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5121_, 0, v___x_5120_);
    leanh::lean_closure_set(v___x_5121_, 1, v___x_5119_);
    return v___x_5121_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5122_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__3_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__3,
    );
    v___x_5123_ = leanh::lean_alloc_closure(
        l_Lean_Parser_atomic_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5123_, 0, v___x_5122_);
    return v___x_5123_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_5124_: u32 = 0;
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5124_ = 93;
    v___x_5125_ = leanh::lean_box_uint32(v___x_5124_);
    return v___x_5125_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5126_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5127_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17_once),
        _init_l_Lake_Toml_stdTable___closed__17,
    );
    v___x_5128_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
    v___x_5129_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5129_, 0, v___x_5128_);
    leanh::lean_closure_set(v___x_5129_, 1, v___x_5127_);
    leanh::lean_closure_set(v___x_5129_, 2, v___x_5126_);
    return v___x_5129_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5130_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__5_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__5,
    );
    v___x_5131_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5132_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5132_, 0, v___x_5131_);
    leanh::lean_closure_set(v___x_5132_, 1, v___x_5130_);
    return v___x_5132_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__6_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__6,
    );
    v___x_5134_ = leanh::lean_alloc_closure(
        l_Lake_Toml_key_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5135_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5135_, 0, v___x_5134_);
    leanh::lean_closure_set(v___x_5135_, 1, v___x_5133_);
    return v___x_5135_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5136_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__7_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__7,
    );
    v___x_5137_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5138_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5138_, 0, v___x_5137_);
    leanh::lean_closure_set(v___x_5138_, 1, v___x_5136_);
    return v___x_5138_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5139_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__8_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__8,
    );
    v___x_5140_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__4_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__4,
    );
    v___x_5141_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5141_, 0, v___x_5140_);
    leanh::lean_closure_set(v___x_5141_, 1, v___x_5139_);
    return v___x_5141_;
}
pub unsafe fn l_Lake_Toml_stdTable_formatter(
    mut v_a_5142_: *mut leanh::LeanObject,
    mut v_a_5143_: *mut leanh::LeanObject,
    mut v_a_5144_: *mut leanh::LeanObject,
    mut v_a_5145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5147_ = l_Lake_Toml_stdTable___closed__0;
    v___x_5148_ = l_Lake_Toml_stdTable___closed__1;
    v___x_5149_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__9_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__9,
    );
    v___x_5150_ = 0;
    v___x_5151_ = l_Lean_Parser_nodeWithAntiquot_formatter(
        v___x_5147_,
        v___x_5148_,
        v___x_5149_,
        v___x_5150_,
        v_a_5142_,
        v_a_5143_,
        v_a_5144_,
        v_a_5145_,
    );
    return v___x_5151_;
}
pub unsafe fn l_Lake_Toml_stdTable_formatter___boxed(
    mut v_a_5152_: *mut leanh::LeanObject,
    mut v_a_5153_: *mut leanh::LeanObject,
    mut v_a_5154_: *mut leanh::LeanObject,
    mut v_a_5155_: *mut leanh::LeanObject,
    mut v_a_5156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5157_ = l_Lake_Toml_stdTable_formatter(v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_);
    leanh::lean_dec(v_a_5155_);
    leanh::lean_dec_ref(v_a_5154_);
    leanh::lean_dec(v_a_5153_);
    leanh::lean_dec_ref(v_a_5152_);
    return v_res_5157_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5158_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__1_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__1,
    );
    v___x_5159_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__0_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__0,
    );
    v___x_5160_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5160_, 0, v___x_5159_);
    leanh::lean_closure_set(v___x_5160_, 1, v___x_5158_);
    return v___x_5160_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5161_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__0_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__0,
    );
    v___x_5162_ = leanh::lean_alloc_closure(
        l_Lean_Parser_atomic_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5162_, 0, v___x_5161_);
    return v___x_5162_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5163_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__5_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__5,
    );
    v___x_5164_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5164_, 0, v___x_5163_);
    leanh::lean_closure_set(v___x_5164_, 1, v___x_5163_);
    return v___x_5164_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5165_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__2_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__2,
    );
    v___x_5166_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5167_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5167_, 0, v___x_5166_);
    leanh::lean_closure_set(v___x_5167_, 1, v___x_5165_);
    return v___x_5167_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5168_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__3_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__3,
    );
    v___x_5169_ = leanh::lean_alloc_closure(
        l_Lake_Toml_key_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5170_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5170_, 0, v___x_5169_);
    leanh::lean_closure_set(v___x_5170_, 1, v___x_5168_);
    return v___x_5170_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5171_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__4_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__4,
    );
    v___x_5172_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5173_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5173_, 0, v___x_5172_);
    leanh::lean_closure_set(v___x_5173_, 1, v___x_5171_);
    return v___x_5173_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5174_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__5_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__5,
    );
    v___x_5175_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__1_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__1,
    );
    v___x_5176_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5176_, 0, v___x_5175_);
    leanh::lean_closure_set(v___x_5176_, 1, v___x_5174_);
    return v___x_5176_;
}
pub unsafe fn l_Lake_Toml_arrayTable_formatter(
    mut v_a_5177_: *mut leanh::LeanObject,
    mut v_a_5178_: *mut leanh::LeanObject,
    mut v_a_5179_: *mut leanh::LeanObject,
    mut v_a_5180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: u8 = 0;
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5182_ = l_Lake_Toml_arrayTable___closed__0;
    v___x_5183_ = l_Lake_Toml_arrayTable___closed__1;
    v___x_5184_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__6_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__6,
    );
    v___x_5185_ = 0;
    v___x_5186_ = l_Lean_Parser_nodeWithAntiquot_formatter(
        v___x_5182_,
        v___x_5183_,
        v___x_5184_,
        v___x_5185_,
        v_a_5177_,
        v_a_5178_,
        v_a_5179_,
        v_a_5180_,
    );
    return v___x_5186_;
}
pub unsafe fn l_Lake_Toml_arrayTable_formatter___boxed(
    mut v_a_5187_: *mut leanh::LeanObject,
    mut v_a_5188_: *mut leanh::LeanObject,
    mut v_a_5189_: *mut leanh::LeanObject,
    mut v_a_5190_: *mut leanh::LeanObject,
    mut v_a_5191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5192_ = l_Lake_Toml_arrayTable_formatter(v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
    leanh::lean_dec(v_a_5190_);
    leanh::lean_dec_ref(v_a_5189_);
    leanh::lean_dec(v_a_5188_);
    leanh::lean_dec_ref(v_a_5187_);
    return v_res_5192_;
}
pub unsafe fn l_Lake_Toml_table_formatter(
    mut v_a_5193_: *mut leanh::LeanObject,
    mut v_a_5194_: *mut leanh::LeanObject,
    mut v_a_5195_: *mut leanh::LeanObject,
    mut v_a_5196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5198_ = leanh::lean_alloc_closure(
        l_Lake_Toml_stdTable_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5199_ = leanh::lean_alloc_closure(
        l_Lake_Toml_arrayTable_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5200_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_5198_,
        v___x_5199_,
        v_a_5193_,
        v_a_5194_,
        v_a_5195_,
        v_a_5196_,
    );
    return v___x_5200_;
}
pub unsafe fn l_Lake_Toml_table_formatter___boxed(
    mut v_a_5201_: *mut leanh::LeanObject,
    mut v_a_5202_: *mut leanh::LeanObject,
    mut v_a_5203_: *mut leanh::LeanObject,
    mut v_a_5204_: *mut leanh::LeanObject,
    mut v_a_5205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5206_ = l_Lake_Toml_table_formatter(v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
    leanh::lean_dec(v_a_5204_);
    leanh::lean_dec_ref(v_a_5203_);
    leanh::lean_dec(v_a_5202_);
    leanh::lean_dec_ref(v_a_5201_);
    return v_res_5206_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(
    mut v_val_5213_: *mut leanh::LeanObject,
    mut v_a_5214_: *mut leanh::LeanObject,
    mut v_a_5215_: *mut leanh::LeanObject,
    mut v_a_5216_: *mut leanh::LeanObject,
    mut v_a_5217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5219_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0;
    v___x_5220_ = leanh::lean_alloc_closure(
        l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5220_, 0, v_val_5213_);
    v___x_5221_ = leanh::lean_alloc_closure(
        l_Lake_Toml_table_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5222_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5222_, 0, v___x_5220_);
    leanh::lean_closure_set(v___x_5222_, 1, v___x_5221_);
    v___x_5223_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_5219_,
        v___x_5222_,
        v_a_5214_,
        v_a_5215_,
        v_a_5216_,
        v_a_5217_,
    );
    return v___x_5223_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed(
    mut v_val_5224_: *mut leanh::LeanObject,
    mut v_a_5225_: *mut leanh::LeanObject,
    mut v_a_5226_: *mut leanh::LeanObject,
    mut v_a_5227_: *mut leanh::LeanObject,
    mut v_a_5228_: *mut leanh::LeanObject,
    mut v_a_5229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5230_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(
        v_val_5224_,
        v_a_5225_,
        v_a_5226_,
        v_a_5227_,
        v_a_5228_,
    );
    leanh::lean_dec(v_a_5228_);
    leanh::lean_dec_ref(v_a_5227_);
    leanh::lean_dec(v_a_5226_);
    leanh::lean_dec_ref(v_a_5225_);
    return v_res_5230_;
}
pub unsafe fn l_Lake_Toml_trailingSep_formatter___redArg() -> *mut leanh::LeanObject {
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5232_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_5232_;
}
pub unsafe fn l_Lake_Toml_trailingSep_formatter___redArg___boxed(
    mut v_a_5233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5234_ = l_Lake_Toml_trailingSep_formatter___redArg();
    return v_res_5234_;
}
pub unsafe fn l_Lake_Toml_trailingSep_formatter(
    mut v_a_5235_: *mut leanh::LeanObject,
    mut v_a_5236_: *mut leanh::LeanObject,
    mut v_a_5237_: *mut leanh::LeanObject,
    mut v_a_5238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5240_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_5240_;
}
pub unsafe fn l_Lake_Toml_trailingSep_formatter___boxed(
    mut v_a_5241_: *mut leanh::LeanObject,
    mut v_a_5242_: *mut leanh::LeanObject,
    mut v_a_5243_: *mut leanh::LeanObject,
    mut v_a_5244_: *mut leanh::LeanObject,
    mut v_a_5245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5246_ = l_Lake_Toml_trailingSep_formatter(v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_);
    leanh::lean_dec(v_a_5244_);
    leanh::lean_dec_ref(v_a_5243_);
    leanh::lean_dec(v_a_5242_);
    leanh::lean_dec_ref(v_a_5241_);
    return v_res_5246_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(
    mut v_val_5247_: *mut leanh::LeanObject,
    mut v_a_5248_: *mut leanh::LeanObject,
    mut v_a_5249_: *mut leanh::LeanObject,
    mut v_a_5250_: *mut leanh::LeanObject,
    mut v_a_5251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5253_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
    v___x_5254_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
    v___x_5255_ = leanh::lean_alloc_closure(
        l_Lake_Toml_header_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5256_ = leanh::lean_alloc_closure(
        l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5256_, 0, v_val_5247_);
    v___x_5257_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingSep_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5258_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5258_, 0, v___x_5256_);
    leanh::lean_closure_set(v___x_5258_, 1, v___x_5257_);
    v___x_5259_ = 1;
    v___x_5260_ = leanh::lean_box((v___x_5259_) as usize);
    v___x_5261_ = leanh::lean_alloc_closure(
        l_Lake_Toml_sepByLinebreak_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5261_, 0, v___x_5258_);
    leanh::lean_closure_set(v___x_5261_, 1, v___x_5260_);
    v___x_5262_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5262_, 0, v___x_5255_);
    leanh::lean_closure_set(v___x_5262_, 1, v___x_5261_);
    v___x_5263_ = l_Lean_Parser_nodeWithAntiquot_formatter(
        v___x_5253_,
        v___x_5254_,
        v___x_5262_,
        v___x_5259_,
        v_a_5248_,
        v_a_5249_,
        v_a_5250_,
        v_a_5251_,
    );
    return v___x_5263_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter___boxed(
    mut v_val_5264_: *mut leanh::LeanObject,
    mut v_a_5265_: *mut leanh::LeanObject,
    mut v_a_5266_: *mut leanh::LeanObject,
    mut v_a_5267_: *mut leanh::LeanObject,
    mut v_a_5268_: *mut leanh::LeanObject,
    mut v_a_5269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5270_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(
        v_val_5264_,
        v_a_5265_,
        v_a_5266_,
        v_a_5267_,
        v_a_5268_,
    );
    leanh::lean_dec(v_a_5268_);
    leanh::lean_dec_ref(v_a_5267_);
    leanh::lean_dec(v_a_5266_);
    leanh::lean_dec_ref(v_a_5265_);
    return v_res_5270_;
}
pub unsafe fn l_Lake_Toml_val_formatter(
    mut v_a_5271_: *mut leanh::LeanObject,
    mut v_a_5272_: *mut leanh::LeanObject,
    mut v_a_5273_: *mut leanh::LeanObject,
    mut v_a_5274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: u8 = 0;
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5276_ = l_Lake_Toml_val___closed__0;
    v___x_5277_ = l_Lake_Toml_val___closed__1;
    v___x_5278_ = l_Lake_Toml_val___closed__2;
    v___x_5279_ = 1;
    v___x_5280_ = l_Lake_Toml_recNodeWithAntiquot_formatter(
        v___x_5276_,
        v___x_5277_,
        v___x_5278_,
        v___x_5279_,
        v_a_5271_,
        v_a_5272_,
        v_a_5273_,
        v_a_5274_,
    );
    return v___x_5280_;
}
pub unsafe fn l_Lake_Toml_val_formatter___boxed(
    mut v_a_5281_: *mut leanh::LeanObject,
    mut v_a_5282_: *mut leanh::LeanObject,
    mut v_a_5283_: *mut leanh::LeanObject,
    mut v_a_5284_: *mut leanh::LeanObject,
    mut v_a_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5286_ = l_Lake_Toml_val_formatter(v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
    leanh::lean_dec(v_a_5284_);
    leanh::lean_dec_ref(v_a_5283_);
    leanh::lean_dec(v_a_5282_);
    leanh::lean_dec_ref(v_a_5281_);
    return v_res_5286_;
}
pub unsafe fn l_Lake_Toml_toml_formatter(
    mut v_a_5287_: *mut leanh::LeanObject,
    mut v_a_5288_: *mut leanh::LeanObject,
    mut v_a_5289_: *mut leanh::LeanObject,
    mut v_a_5290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5292_ = leanh::lean_alloc_closure(
        l_Lake_Toml_val_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5293_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(
        v___x_5292_,
        v_a_5287_,
        v_a_5288_,
        v_a_5289_,
        v_a_5290_,
    );
    return v___x_5293_;
}
pub unsafe fn l_Lake_Toml_toml_formatter___boxed(
    mut v_a_5294_: *mut leanh::LeanObject,
    mut v_a_5295_: *mut leanh::LeanObject,
    mut v_a_5296_: *mut leanh::LeanObject,
    mut v_a_5297_: *mut leanh::LeanObject,
    mut v_a_5298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lake_Toml_toml_formatter(v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_);
    leanh::lean_dec(v_a_5297_);
    leanh::lean_dec_ref(v_a_5296_);
    leanh::lean_dec(v_a_5295_);
    leanh::lean_dec_ref(v_a_5294_);
    return v_res_5299_;
}
pub unsafe fn l_Lake_Toml_header_parenthesizer(
    mut v_a_5300_: *mut leanh::LeanObject,
    mut v_a_5301_: *mut leanh::LeanObject,
    mut v_a_5302_: *mut leanh::LeanObject,
    mut v_a_5303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: u8 = 0;
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5305_ = l_Lake_Toml_header___closed__0;
    v___x_5306_ = l_Lake_Toml_header___closed__1;
    v___x_5307_ = 0;
    v___x_5308_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(
        v___x_5305_,
        v___x_5306_,
        v___x_5307_,
        v_a_5300_,
        v_a_5301_,
        v_a_5302_,
        v_a_5303_,
    );
    return v___x_5308_;
}
pub unsafe fn l_Lake_Toml_header_parenthesizer___boxed(
    mut v_a_5309_: *mut leanh::LeanObject,
    mut v_a_5310_: *mut leanh::LeanObject,
    mut v_a_5311_: *mut leanh::LeanObject,
    mut v_a_5312_: *mut leanh::LeanObject,
    mut v_a_5313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_Lake_Toml_header_parenthesizer(v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_);
    leanh::lean_dec(v_a_5312_);
    leanh::lean_dec_ref(v_a_5311_);
    leanh::lean_dec(v_a_5310_);
    leanh::lean_dec_ref(v_a_5309_);
    return v_res_5314_;
}
pub unsafe fn l_Lake_Toml_unquotedKey_parenthesizer(
    mut v_a_5315_: *mut leanh::LeanObject,
    mut v_a_5316_: *mut leanh::LeanObject,
    mut v_a_5317_: *mut leanh::LeanObject,
    mut v_a_5318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u8 = 0;
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5320_ = l_Lake_Toml_unquotedKey___closed__0;
    v___x_5321_ = l_Lake_Toml_unquotedKey___closed__1;
    v___x_5322_ = 0;
    v___x_5323_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(
        v___x_5320_,
        v___x_5321_,
        v___x_5322_,
        v_a_5315_,
        v_a_5316_,
        v_a_5317_,
        v_a_5318_,
    );
    return v___x_5323_;
}
pub unsafe fn l_Lake_Toml_unquotedKey_parenthesizer___boxed(
    mut v_a_5324_: *mut leanh::LeanObject,
    mut v_a_5325_: *mut leanh::LeanObject,
    mut v_a_5326_: *mut leanh::LeanObject,
    mut v_a_5327_: *mut leanh::LeanObject,
    mut v_a_5328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5329_ = l_Lake_Toml_unquotedKey_parenthesizer(v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_);
    leanh::lean_dec(v_a_5327_);
    leanh::lean_dec_ref(v_a_5326_);
    leanh::lean_dec(v_a_5325_);
    leanh::lean_dec_ref(v_a_5324_);
    return v_res_5329_;
}
pub unsafe fn l_Lake_Toml_basicString_parenthesizer(
    mut v_a_5330_: *mut leanh::LeanObject,
    mut v_a_5331_: *mut leanh::LeanObject,
    mut v_a_5332_: *mut leanh::LeanObject,
    mut v_a_5333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: u8 = 0;
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5335_ = l_Lake_Toml_basicString___closed__0;
    v___x_5336_ = l_Lake_Toml_basicString___closed__1;
    v___x_5337_ = 0;
    v___x_5338_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(
        v___x_5335_,
        v___x_5336_,
        v___x_5337_,
        v_a_5330_,
        v_a_5331_,
        v_a_5332_,
        v_a_5333_,
    );
    return v___x_5338_;
}
pub unsafe fn l_Lake_Toml_basicString_parenthesizer___boxed(
    mut v_a_5339_: *mut leanh::LeanObject,
    mut v_a_5340_: *mut leanh::LeanObject,
    mut v_a_5341_: *mut leanh::LeanObject,
    mut v_a_5342_: *mut leanh::LeanObject,
    mut v_a_5343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5344_ = l_Lake_Toml_basicString_parenthesizer(v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_);
    leanh::lean_dec(v_a_5342_);
    leanh::lean_dec_ref(v_a_5341_);
    leanh::lean_dec(v_a_5340_);
    leanh::lean_dec_ref(v_a_5339_);
    return v_res_5344_;
}
pub unsafe fn l_Lake_Toml_literalString_parenthesizer(
    mut v_a_5345_: *mut leanh::LeanObject,
    mut v_a_5346_: *mut leanh::LeanObject,
    mut v_a_5347_: *mut leanh::LeanObject,
    mut v_a_5348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: u8 = 0;
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5350_ = l_Lake_Toml_literalString___closed__0;
    v___x_5351_ = l_Lake_Toml_literalString___closed__1;
    v___x_5352_ = 0;
    v___x_5353_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(
        v___x_5350_,
        v___x_5351_,
        v___x_5352_,
        v_a_5345_,
        v_a_5346_,
        v_a_5347_,
        v_a_5348_,
    );
    return v___x_5353_;
}
pub unsafe fn l_Lake_Toml_literalString_parenthesizer___boxed(
    mut v_a_5354_: *mut leanh::LeanObject,
    mut v_a_5355_: *mut leanh::LeanObject,
    mut v_a_5356_: *mut leanh::LeanObject,
    mut v_a_5357_: *mut leanh::LeanObject,
    mut v_a_5358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5359_ =
        l_Lake_Toml_literalString_parenthesizer(v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_);
    leanh::lean_dec(v_a_5357_);
    leanh::lean_dec_ref(v_a_5356_);
    leanh::lean_dec(v_a_5355_);
    leanh::lean_dec_ref(v_a_5354_);
    return v_res_5359_;
}
pub unsafe fn l_Lake_Toml_quotedKey_parenthesizer(
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_a_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5365_ = leanh::lean_alloc_closure(
        l_Lake_Toml_basicString_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5366_ = leanh::lean_alloc_closure(
        l_Lake_Toml_literalString_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5367_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(
        v___x_5365_,
        v___x_5366_,
        v_a_5360_,
        v_a_5361_,
        v_a_5362_,
        v_a_5363_,
    );
    return v___x_5367_;
}
pub unsafe fn l_Lake_Toml_quotedKey_parenthesizer___boxed(
    mut v_a_5368_: *mut leanh::LeanObject,
    mut v_a_5369_: *mut leanh::LeanObject,
    mut v_a_5370_: *mut leanh::LeanObject,
    mut v_a_5371_: *mut leanh::LeanObject,
    mut v_a_5372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5373_ = l_Lake_Toml_quotedKey_parenthesizer(v_a_5368_, v_a_5369_, v_a_5370_, v_a_5371_);
    leanh::lean_dec(v_a_5371_);
    leanh::lean_dec_ref(v_a_5370_);
    leanh::lean_dec(v_a_5369_);
    leanh::lean_dec_ref(v_a_5368_);
    return v_res_5373_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5374_ = leanh::lean_alloc_closure(
        l_Lake_Toml_quotedKey_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5375_ = leanh::lean_alloc_closure(
        l_Lake_Toml_unquotedKey_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5376_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5376_, 0, v___x_5375_);
    leanh::lean_closure_set(v___x_5376_, 1, v___x_5374_);
    return v___x_5376_;
}
pub unsafe fn l_Lake_Toml_simpleKey_parenthesizer(
    mut v_a_5377_: *mut leanh::LeanObject,
    mut v_a_5378_: *mut leanh::LeanObject,
    mut v_a_5379_: *mut leanh::LeanObject,
    mut v_a_5380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: u8 = 0;
    let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5382_ = l_Lake_Toml_simpleKey___closed__0;
    v___x_5383_ = l_Lake_Toml_simpleKey___closed__1;
    v___x_5384_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0,
    );
    v___x_5385_ = 1;
    v___x_5386_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(
        v___x_5382_,
        v___x_5383_,
        v___x_5384_,
        v___x_5385_,
        v_a_5377_,
        v_a_5378_,
        v_a_5379_,
        v_a_5380_,
    );
    return v___x_5386_;
}
pub unsafe fn l_Lake_Toml_simpleKey_parenthesizer___boxed(
    mut v_a_5387_: *mut leanh::LeanObject,
    mut v_a_5388_: *mut leanh::LeanObject,
    mut v_a_5389_: *mut leanh::LeanObject,
    mut v_a_5390_: *mut leanh::LeanObject,
    mut v_a_5391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5392_ = l_Lake_Toml_simpleKey_parenthesizer(v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_);
    leanh::lean_dec(v_a_5390_);
    leanh::lean_dec_ref(v_a_5389_);
    leanh::lean_dec(v_a_5388_);
    leanh::lean_dec_ref(v_a_5387_);
    return v_res_5392_;
}
pub unsafe fn l_Lake_Toml_trailingWs_parenthesizer___redArg() -> *mut leanh::LeanObject {
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_5394_;
}
pub unsafe fn l_Lake_Toml_trailingWs_parenthesizer___redArg___boxed(
    mut v_a_5395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5396_ = l_Lake_Toml_trailingWs_parenthesizer___redArg();
    return v_res_5396_;
}
pub unsafe fn l_Lake_Toml_trailingWs_parenthesizer(
    mut v_a_5397_: *mut leanh::LeanObject,
    mut v_a_5398_: *mut leanh::LeanObject,
    mut v_a_5399_: *mut leanh::LeanObject,
    mut v_a_5400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5402_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_5402_;
}
pub unsafe fn l_Lake_Toml_trailingWs_parenthesizer___boxed(
    mut v_a_5403_: *mut leanh::LeanObject,
    mut v_a_5404_: *mut leanh::LeanObject,
    mut v_a_5405_: *mut leanh::LeanObject,
    mut v_a_5406_: *mut leanh::LeanObject,
    mut v_a_5407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5408_ = l_Lake_Toml_trailingWs_parenthesizer(v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
    leanh::lean_dec(v_a_5406_);
    leanh::lean_dec_ref(v_a_5405_);
    leanh::lean_dec(v_a_5404_);
    leanh::lean_dec_ref(v_a_5403_);
    return v_res_5408_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5409_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5410_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7_once),
        _init_l_Lake_Toml_key___closed__7,
    );
    v___x_5411_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
    v___x_5412_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5412_, 0, v___x_5411_);
    leanh::lean_closure_set(v___x_5412_, 1, v___x_5410_);
    leanh::lean_closure_set(v___x_5412_, 2, v___x_5409_);
    return v___x_5412_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5413_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5414_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__0,
    );
    v___x_5415_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5415_, 0, v___x_5414_);
    leanh::lean_closure_set(v___x_5415_, 1, v___x_5413_);
    return v___x_5415_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5416_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__1_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__1,
    );
    v___x_5417_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5418_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5418_, 0, v___x_5417_);
    leanh::lean_closure_set(v___x_5418_, 1, v___x_5416_);
    return v___x_5418_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_5419_: u8 = 0;
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5419_ = 0;
    v___x_5420_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__2_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__2,
    );
    v___x_5421_ = l_Lake_Toml_key___closed__3;
    v___x_5422_ = leanh::lean_alloc_closure(
        l_Lake_Toml_simpleKey_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5423_ = leanh::lean_box((v___x_5419_) as usize);
    v___x_5424_ = leanh::lean_alloc_closure(
        l_Lean_Parser_sepBy1_parenthesizer___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_5424_, 0, v___x_5422_);
    leanh::lean_closure_set(v___x_5424_, 1, v___x_5421_);
    leanh::lean_closure_set(v___x_5424_, 2, v___x_5420_);
    leanh::lean_closure_set(v___x_5424_, 3, v___x_5423_);
    return v___x_5424_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5425_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__3_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__3,
    );
    v___x_5426_ = l_Lake_Toml_key___closed__2;
    v___x_5427_ = leanh::lean_alloc_closure(
        l_Lean_Parser_setExpected_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5427_, 0, v___x_5426_);
    leanh::lean_closure_set(v___x_5427_, 1, v___x_5425_);
    return v___x_5427_;
}
pub unsafe fn l_Lake_Toml_key_parenthesizer(
    mut v_a_5428_: *mut leanh::LeanObject,
    mut v_a_5429_: *mut leanh::LeanObject,
    mut v_a_5430_: *mut leanh::LeanObject,
    mut v_a_5431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: u8 = 0;
    let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5433_ = l_Lake_Toml_key___closed__0;
    v___x_5434_ = l_Lake_Toml_key___closed__1;
    v___x_5435_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__4_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__4,
    );
    v___x_5436_ = 1;
    v___x_5437_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(
        v___x_5433_,
        v___x_5434_,
        v___x_5435_,
        v___x_5436_,
        v_a_5428_,
        v_a_5429_,
        v_a_5430_,
        v_a_5431_,
    );
    return v___x_5437_;
}
pub unsafe fn l_Lake_Toml_key_parenthesizer___boxed(
    mut v_a_5438_: *mut leanh::LeanObject,
    mut v_a_5439_: *mut leanh::LeanObject,
    mut v_a_5440_: *mut leanh::LeanObject,
    mut v_a_5441_: *mut leanh::LeanObject,
    mut v_a_5442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5443_ = l_Lake_Toml_key_parenthesizer(v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_);
    leanh::lean_dec(v_a_5441_);
    leanh::lean_dec_ref(v_a_5440_);
    leanh::lean_dec(v_a_5439_);
    leanh::lean_dec_ref(v_a_5438_);
    return v_res_5443_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5444_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5445_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5,
    );
    v___x_5446_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
    v___x_5447_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5447_, 0, v___x_5446_);
    leanh::lean_closure_set(v___x_5447_, 1, v___x_5445_);
    leanh::lean_closure_set(v___x_5447_, 2, v___x_5444_);
    return v___x_5447_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(
    mut v_val_5448_: *mut leanh::LeanObject,
    mut v_a_5449_: *mut leanh::LeanObject,
    mut v_a_5450_: *mut leanh::LeanObject,
    mut v_a_5451_: *mut leanh::LeanObject,
    mut v_a_5452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: u8 = 0;
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5454_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
    v___x_5455_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
    v___x_5456_ = leanh::lean_alloc_closure(
        l_Lake_Toml_key_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5457_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5458_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0,
    );
    leanh::lean_inc_ref(v___x_5457_);
    v___x_5459_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5459_, 0, v___x_5457_);
    leanh::lean_closure_set(v___x_5459_, 1, v_val_5448_);
    v___x_5460_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5460_, 0, v___x_5458_);
    leanh::lean_closure_set(v___x_5460_, 1, v___x_5459_);
    v___x_5461_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5461_, 0, v___x_5457_);
    leanh::lean_closure_set(v___x_5461_, 1, v___x_5460_);
    v___x_5462_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5462_, 0, v___x_5456_);
    leanh::lean_closure_set(v___x_5462_, 1, v___x_5461_);
    v___x_5463_ = 1;
    v___x_5464_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(
        v___x_5454_,
        v___x_5455_,
        v___x_5462_,
        v___x_5463_,
        v_a_5449_,
        v_a_5450_,
        v_a_5451_,
        v_a_5452_,
    );
    return v___x_5464_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed(
    mut v_val_5465_: *mut leanh::LeanObject,
    mut v_a_5466_: *mut leanh::LeanObject,
    mut v_a_5467_: *mut leanh::LeanObject,
    mut v_a_5468_: *mut leanh::LeanObject,
    mut v_a_5469_: *mut leanh::LeanObject,
    mut v_a_5470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5471_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(
        v_val_5465_,
        v_a_5466_,
        v_a_5467_,
        v_a_5468_,
        v_a_5469_,
    );
    leanh::lean_dec(v_a_5469_);
    leanh::lean_dec_ref(v_a_5468_);
    leanh::lean_dec(v_a_5467_);
    leanh::lean_dec_ref(v_a_5466_);
    return v_res_5471_;
}
pub unsafe fn l_Lake_Toml_stdTable_parenthesizer___lam__0(
    mut v___x_5472_: *mut leanh::LeanObject,
    mut v___x_5473_: *mut leanh::LeanObject,
    mut v___y_5474_: *mut leanh::LeanObject,
    mut v___y_5475_: *mut leanh::LeanObject,
    mut v___y_5476_: *mut leanh::LeanObject,
    mut v___y_5477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5479_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(
        v___x_5472_,
        v___x_5473_,
        v___y_5474_,
        v___y_5475_,
        v___y_5476_,
        v___y_5477_,
    );
    return v___x_5479_;
}
pub unsafe fn l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed(
    mut v___x_5480_: *mut leanh::LeanObject,
    mut v___x_5481_: *mut leanh::LeanObject,
    mut v___y_5482_: *mut leanh::LeanObject,
    mut v___y_5483_: *mut leanh::LeanObject,
    mut v___y_5484_: *mut leanh::LeanObject,
    mut v___y_5485_: *mut leanh::LeanObject,
    mut v___y_5486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5487_ = l_Lake_Toml_stdTable_parenthesizer___lam__0(
        v___x_5480_,
        v___x_5481_,
        v___y_5482_,
        v___y_5483_,
        v___y_5484_,
        v___y_5485_,
    );
    leanh::lean_dec(v___y_5485_);
    leanh::lean_dec_ref(v___y_5484_);
    leanh::lean_dec(v___y_5483_);
    leanh::lean_dec_ref(v___y_5482_);
    return v_res_5487_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5488_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5489_ = l_Lake_Toml_stdTable___closed__3;
    v___x_5490_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
    v___x_5491_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5491_, 0, v___x_5490_);
    leanh::lean_closure_set(v___x_5491_, 1, v___x_5489_);
    leanh::lean_closure_set(v___x_5491_, 2, v___x_5488_);
    return v___x_5491_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5492_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5493_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8_once),
        _init_l_Lake_Toml_stdTable___closed__8,
    );
    v___x_5494_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
    v___x_5495_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5495_, 0, v___x_5494_);
    leanh::lean_closure_set(v___x_5495_, 1, v___x_5493_);
    leanh::lean_closure_set(v___x_5495_, 2, v___x_5492_);
    return v___x_5495_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5496_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__1_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__1,
    );
    v___x_5497_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5497_, 0, v___x_5496_);
    return v___x_5497_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5498_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__2_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__2,
    );
    v___x_5499_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__0,
    );
    v___f_5500_ = leanh::lean_alloc_closure(
        l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_5500_, 0, v___x_5499_);
    leanh::lean_closure_set(v___f_5500_, 1, v___x_5498_);
    return v___f_5500_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5501_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5502_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17_once),
        _init_l_Lake_Toml_stdTable___closed__17,
    );
    v___x_5503_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
    v___x_5504_ = leanh::lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_5504_, 0, v___x_5503_);
    leanh::lean_closure_set(v___x_5504_, 1, v___x_5502_);
    leanh::lean_closure_set(v___x_5504_, 2, v___x_5501_);
    return v___x_5504_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5505_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__4_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__4,
    );
    v___x_5506_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5507_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5507_, 0, v___x_5506_);
    leanh::lean_closure_set(v___x_5507_, 1, v___x_5505_);
    return v___x_5507_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__5_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__5,
    );
    v___x_5509_ = leanh::lean_alloc_closure(
        l_Lake_Toml_key_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5510_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5510_, 0, v___x_5509_);
    leanh::lean_closure_set(v___x_5510_, 1, v___x_5508_);
    return v___x_5510_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5511_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__6_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__6,
    );
    v___x_5512_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5513_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5513_, 0, v___x_5512_);
    leanh::lean_closure_set(v___x_5513_, 1, v___x_5511_);
    return v___x_5513_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5514_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__7_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__7,
    );
    v___f_5515_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__3_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__3,
    );
    v___x_5516_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5516_, 0, v___f_5515_);
    leanh::lean_closure_set(v___x_5516_, 1, v___x_5514_);
    return v___x_5516_;
}
pub unsafe fn l_Lake_Toml_stdTable_parenthesizer(
    mut v_a_5517_: *mut leanh::LeanObject,
    mut v_a_5518_: *mut leanh::LeanObject,
    mut v_a_5519_: *mut leanh::LeanObject,
    mut v_a_5520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: u8 = 0;
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5522_ = l_Lake_Toml_stdTable___closed__0;
    v___x_5523_ = l_Lake_Toml_stdTable___closed__1;
    v___x_5524_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__8_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__8,
    );
    v___x_5525_ = 0;
    v___x_5526_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(
        v___x_5522_,
        v___x_5523_,
        v___x_5524_,
        v___x_5525_,
        v_a_5517_,
        v_a_5518_,
        v_a_5519_,
        v_a_5520_,
    );
    return v___x_5526_;
}
pub unsafe fn l_Lake_Toml_stdTable_parenthesizer___boxed(
    mut v_a_5527_: *mut leanh::LeanObject,
    mut v_a_5528_: *mut leanh::LeanObject,
    mut v_a_5529_: *mut leanh::LeanObject,
    mut v_a_5530_: *mut leanh::LeanObject,
    mut v_a_5531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5532_ = l_Lake_Toml_stdTable_parenthesizer(v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_);
    leanh::lean_dec(v_a_5530_);
    leanh::lean_dec_ref(v_a_5529_);
    leanh::lean_dec(v_a_5528_);
    leanh::lean_dec_ref(v_a_5527_);
    return v_res_5532_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5533_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__1_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__1,
    );
    v___x_5534_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__0,
    );
    v___f_5535_ = leanh::lean_alloc_closure(
        l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_5535_, 0, v___x_5534_);
    leanh::lean_closure_set(v___f_5535_, 1, v___x_5533_);
    return v___f_5535_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5536_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__4_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__4,
    );
    v___x_5537_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5537_, 0, v___x_5536_);
    leanh::lean_closure_set(v___x_5537_, 1, v___x_5536_);
    return v___x_5537_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5538_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__1_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1,
    );
    v___x_5539_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5540_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5540_, 0, v___x_5539_);
    leanh::lean_closure_set(v___x_5540_, 1, v___x_5538_);
    return v___x_5540_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5541_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__2_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2,
    );
    v___x_5542_ = leanh::lean_alloc_closure(
        l_Lake_Toml_key_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5543_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5543_, 0, v___x_5542_);
    leanh::lean_closure_set(v___x_5543_, 1, v___x_5541_);
    return v___x_5543_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5544_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__3_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3,
    );
    v___x_5545_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5546_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5546_, 0, v___x_5545_);
    leanh::lean_closure_set(v___x_5546_, 1, v___x_5544_);
    return v___x_5546_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5547_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__4_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4,
    );
    v___f_5548_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0,
    );
    v___x_5549_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5549_, 0, v___f_5548_);
    leanh::lean_closure_set(v___x_5549_, 1, v___x_5547_);
    return v___x_5549_;
}
pub unsafe fn l_Lake_Toml_arrayTable_parenthesizer(
    mut v_a_5550_: *mut leanh::LeanObject,
    mut v_a_5551_: *mut leanh::LeanObject,
    mut v_a_5552_: *mut leanh::LeanObject,
    mut v_a_5553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: u8 = 0;
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5555_ = l_Lake_Toml_arrayTable___closed__0;
    v___x_5556_ = l_Lake_Toml_arrayTable___closed__1;
    v___x_5557_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__5_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5,
    );
    v___x_5558_ = 0;
    v___x_5559_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(
        v___x_5555_,
        v___x_5556_,
        v___x_5557_,
        v___x_5558_,
        v_a_5550_,
        v_a_5551_,
        v_a_5552_,
        v_a_5553_,
    );
    return v___x_5559_;
}
pub unsafe fn l_Lake_Toml_arrayTable_parenthesizer___boxed(
    mut v_a_5560_: *mut leanh::LeanObject,
    mut v_a_5561_: *mut leanh::LeanObject,
    mut v_a_5562_: *mut leanh::LeanObject,
    mut v_a_5563_: *mut leanh::LeanObject,
    mut v_a_5564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5565_ = l_Lake_Toml_arrayTable_parenthesizer(v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_);
    leanh::lean_dec(v_a_5563_);
    leanh::lean_dec_ref(v_a_5562_);
    leanh::lean_dec(v_a_5561_);
    leanh::lean_dec_ref(v_a_5560_);
    return v_res_5565_;
}
pub unsafe fn l_Lake_Toml_table_parenthesizer(
    mut v_a_5566_: *mut leanh::LeanObject,
    mut v_a_5567_: *mut leanh::LeanObject,
    mut v_a_5568_: *mut leanh::LeanObject,
    mut v_a_5569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5571_ = leanh::lean_alloc_closure(
        l_Lake_Toml_stdTable_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5572_ = leanh::lean_alloc_closure(
        l_Lake_Toml_arrayTable_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5573_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(
        v___x_5571_,
        v___x_5572_,
        v_a_5566_,
        v_a_5567_,
        v_a_5568_,
        v_a_5569_,
    );
    return v___x_5573_;
}
pub unsafe fn l_Lake_Toml_table_parenthesizer___boxed(
    mut v_a_5574_: *mut leanh::LeanObject,
    mut v_a_5575_: *mut leanh::LeanObject,
    mut v_a_5576_: *mut leanh::LeanObject,
    mut v_a_5577_: *mut leanh::LeanObject,
    mut v_a_5578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5579_ = l_Lake_Toml_table_parenthesizer(v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_);
    leanh::lean_dec(v_a_5577_);
    leanh::lean_dec_ref(v_a_5576_);
    leanh::lean_dec(v_a_5575_);
    leanh::lean_dec_ref(v_a_5574_);
    return v_res_5579_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(
    mut v_val_5586_: *mut leanh::LeanObject,
    mut v_a_5587_: *mut leanh::LeanObject,
    mut v_a_5588_: *mut leanh::LeanObject,
    mut v_a_5589_: *mut leanh::LeanObject,
    mut v_a_5590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5592_ =
        l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0;
    v___x_5593_ = leanh::lean_alloc_closure(
        l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5593_, 0, v_val_5586_);
    v___x_5594_ = leanh::lean_alloc_closure(
        l_Lake_Toml_table_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5595_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5595_, 0, v___x_5593_);
    leanh::lean_closure_set(v___x_5595_, 1, v___x_5594_);
    v___x_5596_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_5592_,
        v___x_5595_,
        v_a_5587_,
        v_a_5588_,
        v_a_5589_,
        v_a_5590_,
    );
    return v___x_5596_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed(
    mut v_val_5597_: *mut leanh::LeanObject,
    mut v_a_5598_: *mut leanh::LeanObject,
    mut v_a_5599_: *mut leanh::LeanObject,
    mut v_a_5600_: *mut leanh::LeanObject,
    mut v_a_5601_: *mut leanh::LeanObject,
    mut v_a_5602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5603_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(
        v_val_5597_,
        v_a_5598_,
        v_a_5599_,
        v_a_5600_,
        v_a_5601_,
    );
    leanh::lean_dec(v_a_5601_);
    leanh::lean_dec_ref(v_a_5600_);
    leanh::lean_dec(v_a_5599_);
    leanh::lean_dec_ref(v_a_5598_);
    return v_res_5603_;
}
pub unsafe fn l_Lake_Toml_trailingSep_parenthesizer___redArg() -> *mut leanh::LeanObject {
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5605_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_5605_;
}
pub unsafe fn l_Lake_Toml_trailingSep_parenthesizer___redArg___boxed(
    mut v_a_5606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5607_ = l_Lake_Toml_trailingSep_parenthesizer___redArg();
    return v_res_5607_;
}
pub unsafe fn l_Lake_Toml_trailingSep_parenthesizer(
    mut v_a_5608_: *mut leanh::LeanObject,
    mut v_a_5609_: *mut leanh::LeanObject,
    mut v_a_5610_: *mut leanh::LeanObject,
    mut v_a_5611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5613_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_5613_;
}
pub unsafe fn l_Lake_Toml_trailingSep_parenthesizer___boxed(
    mut v_a_5614_: *mut leanh::LeanObject,
    mut v_a_5615_: *mut leanh::LeanObject,
    mut v_a_5616_: *mut leanh::LeanObject,
    mut v_a_5617_: *mut leanh::LeanObject,
    mut v_a_5618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5619_ = l_Lake_Toml_trailingSep_parenthesizer(v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_);
    leanh::lean_dec(v_a_5617_);
    leanh::lean_dec_ref(v_a_5616_);
    leanh::lean_dec(v_a_5615_);
    leanh::lean_dec_ref(v_a_5614_);
    return v_res_5619_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(
    mut v_val_5620_: *mut leanh::LeanObject,
    mut v_a_5621_: *mut leanh::LeanObject,
    mut v_a_5622_: *mut leanh::LeanObject,
    mut v_a_5623_: *mut leanh::LeanObject,
    mut v_a_5624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: u8 = 0;
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5626_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
    v___x_5627_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
    v___x_5628_ = leanh::lean_alloc_closure(
        l_Lake_Toml_header_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5629_ = leanh::lean_alloc_closure(
        l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_5629_, 0, v_val_5620_);
    v___x_5630_ = leanh::lean_alloc_closure(
        l_Lake_Toml_trailingSep_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5631_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5631_, 0, v___x_5629_);
    leanh::lean_closure_set(v___x_5631_, 1, v___x_5630_);
    v___x_5632_ = 1;
    v___x_5633_ = leanh::lean_box((v___x_5632_) as usize);
    v___x_5634_ = leanh::lean_alloc_closure(
        l_Lake_Toml_sepByLinebreak_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5634_, 0, v___x_5631_);
    leanh::lean_closure_set(v___x_5634_, 1, v___x_5633_);
    v___x_5635_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_5635_, 0, v___x_5628_);
    leanh::lean_closure_set(v___x_5635_, 1, v___x_5634_);
    v___x_5636_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(
        v___x_5626_,
        v___x_5627_,
        v___x_5635_,
        v___x_5632_,
        v_a_5621_,
        v_a_5622_,
        v_a_5623_,
        v_a_5624_,
    );
    return v___x_5636_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer___boxed(
    mut v_val_5637_: *mut leanh::LeanObject,
    mut v_a_5638_: *mut leanh::LeanObject,
    mut v_a_5639_: *mut leanh::LeanObject,
    mut v_a_5640_: *mut leanh::LeanObject,
    mut v_a_5641_: *mut leanh::LeanObject,
    mut v_a_5642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5643_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(
        v_val_5637_,
        v_a_5638_,
        v_a_5639_,
        v_a_5640_,
        v_a_5641_,
    );
    leanh::lean_dec(v_a_5641_);
    leanh::lean_dec_ref(v_a_5640_);
    leanh::lean_dec(v_a_5639_);
    leanh::lean_dec_ref(v_a_5638_);
    return v_res_5643_;
}
pub unsafe fn l_Lake_Toml_val_parenthesizer(
    mut v_a_5644_: *mut leanh::LeanObject,
    mut v_a_5645_: *mut leanh::LeanObject,
    mut v_a_5646_: *mut leanh::LeanObject,
    mut v_a_5647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: u8 = 0;
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5649_ = l_Lake_Toml_val___closed__0;
    v___x_5650_ = l_Lake_Toml_val___closed__1;
    v___x_5651_ = l_Lake_Toml_val___closed__2;
    v___x_5652_ = 1;
    v___x_5653_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(
        v___x_5649_,
        v___x_5650_,
        v___x_5651_,
        v___x_5652_,
        v_a_5644_,
        v_a_5645_,
        v_a_5646_,
        v_a_5647_,
    );
    return v___x_5653_;
}
pub unsafe fn l_Lake_Toml_val_parenthesizer___boxed(
    mut v_a_5654_: *mut leanh::LeanObject,
    mut v_a_5655_: *mut leanh::LeanObject,
    mut v_a_5656_: *mut leanh::LeanObject,
    mut v_a_5657_: *mut leanh::LeanObject,
    mut v_a_5658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5659_ = l_Lake_Toml_val_parenthesizer(v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_);
    leanh::lean_dec(v_a_5657_);
    leanh::lean_dec_ref(v_a_5656_);
    leanh::lean_dec(v_a_5655_);
    leanh::lean_dec_ref(v_a_5654_);
    return v_res_5659_;
}
pub unsafe fn l_Lake_Toml_toml_parenthesizer(
    mut v_a_5660_: *mut leanh::LeanObject,
    mut v_a_5661_: *mut leanh::LeanObject,
    mut v_a_5662_: *mut leanh::LeanObject,
    mut v_a_5663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5665_ = leanh::lean_alloc_closure(
        l_Lake_Toml_val_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5666_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(
        v___x_5665_,
        v_a_5660_,
        v_a_5661_,
        v_a_5662_,
        v_a_5663_,
    );
    return v___x_5666_;
}
pub unsafe fn l_Lake_Toml_toml_parenthesizer___boxed(
    mut v_a_5667_: *mut leanh::LeanObject,
    mut v_a_5668_: *mut leanh::LeanObject,
    mut v_a_5669_: *mut leanh::LeanObject,
    mut v_a_5670_: *mut leanh::LeanObject,
    mut v_a_5671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5672_ = l_Lake_Toml_toml_parenthesizer(v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_);
    leanh::lean_dec(v_a_5670_);
    leanh::lean_dec_ref(v_a_5669_);
    leanh::lean_dec(v_a_5668_);
    leanh::lean_dec_ref(v_a_5667_);
    return v_res_5672_;
}
pub unsafe fn _init_l_Lake_Toml_toml___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5673_ = l_Lake_Toml_val;
    v___x_5674_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(v___x_5673_);
    return v___x_5674_;
}
pub unsafe fn _init_l_Lake_Toml_toml___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5675_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_toml___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_toml___closed__0_once),
        _init_l_Lake_Toml_toml___closed__0,
    );
    v___x_5676_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
    v___x_5677_ = l_Lean_Parser_withCache(v___x_5676_, v___x_5675_);
    return v___x_5677_;
}
pub unsafe fn _init_l_Lake_Toml_toml() -> *mut leanh::LeanObject {
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5678_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_toml___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_toml___closed__1_once),
        _init_l_Lake_Toml_toml___closed__1,
    );
    return v___x_5678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Grammar(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Toml_ParserUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_Toml_trailingWs = _init_l_Lake_Toml_trailingWs();
    leanh::lean_mark_persistent(l_Lake_Toml_trailingWs);
    l_Lake_Toml_trailingSep = _init_l_Lake_Toml_trailingSep();
    leanh::lean_mark_persistent(l_Lake_Toml_trailingSep);
    l_Lake_Toml_unquotedKey = _init_l_Lake_Toml_unquotedKey();
    leanh::lean_mark_persistent(l_Lake_Toml_unquotedKey);
    l_Lake_Toml_basicString = _init_l_Lake_Toml_basicString();
    leanh::lean_mark_persistent(l_Lake_Toml_basicString);
    l_Lake_Toml_literalString = _init_l_Lake_Toml_literalString();
    leanh::lean_mark_persistent(l_Lake_Toml_literalString);
    l_Lake_Toml_mlBasicString = _init_l_Lake_Toml_mlBasicString();
    leanh::lean_mark_persistent(l_Lake_Toml_mlBasicString);
    l_Lake_Toml_mlLiteralString = _init_l_Lake_Toml_mlLiteralString();
    leanh::lean_mark_persistent(l_Lake_Toml_mlLiteralString);
    l_Lake_Toml_quotedKey = _init_l_Lake_Toml_quotedKey();
    leanh::lean_mark_persistent(l_Lake_Toml_quotedKey);
    l_Lake_Toml_simpleKey = _init_l_Lake_Toml_simpleKey();
    leanh::lean_mark_persistent(l_Lake_Toml_simpleKey);
    l_Lake_Toml_key = _init_l_Lake_Toml_key();
    leanh::lean_mark_persistent(l_Lake_Toml_key);
    l_Lake_Toml_stdTable = _init_l_Lake_Toml_stdTable();
    leanh::lean_mark_persistent(l_Lake_Toml_stdTable);
    l_Lake_Toml_arrayTable = _init_l_Lake_Toml_arrayTable();
    leanh::lean_mark_persistent(l_Lake_Toml_arrayTable);
    l_Lake_Toml_table = _init_l_Lake_Toml_table();
    leanh::lean_mark_persistent(l_Lake_Toml_table);
    l_Lake_Toml_header = _init_l_Lake_Toml_header();
    leanh::lean_mark_persistent(l_Lake_Toml_header);
    l_Lake_Toml_string = _init_l_Lake_Toml_string();
    leanh::lean_mark_persistent(l_Lake_Toml_string);
    l_Lake_Toml_true = _init_l_Lake_Toml_true();
    leanh::lean_mark_persistent(l_Lake_Toml_true);
    l_Lake_Toml_false = _init_l_Lake_Toml_false();
    leanh::lean_mark_persistent(l_Lake_Toml_false);
    l_Lake_Toml_boolean = _init_l_Lake_Toml_boolean();
    leanh::lean_mark_persistent(l_Lake_Toml_boolean);
    l_Lake_Toml_numeralAntiquot = _init_l_Lake_Toml_numeralAntiquot();
    leanh::lean_mark_persistent(l_Lake_Toml_numeralAntiquot);
    l_Lake_Toml_numeral = _init_l_Lake_Toml_numeral();
    leanh::lean_mark_persistent(l_Lake_Toml_numeral);
    l_Lake_Toml_float = _init_l_Lake_Toml_float();
    leanh::lean_mark_persistent(l_Lake_Toml_float);
    l_Lake_Toml_decInt = _init_l_Lake_Toml_decInt();
    leanh::lean_mark_persistent(l_Lake_Toml_decInt);
    l_Lake_Toml_binNum = _init_l_Lake_Toml_binNum();
    leanh::lean_mark_persistent(l_Lake_Toml_binNum);
    l_Lake_Toml_octNum = _init_l_Lake_Toml_octNum();
    leanh::lean_mark_persistent(l_Lake_Toml_octNum);
    l_Lake_Toml_hexNum = _init_l_Lake_Toml_hexNum();
    leanh::lean_mark_persistent(l_Lake_Toml_hexNum);
    l_Lake_Toml_dateTime = _init_l_Lake_Toml_dateTime();
    leanh::lean_mark_persistent(l_Lake_Toml_dateTime);
    l_Lake_Toml_val = _init_l_Lake_Toml_val();
    leanh::lean_mark_persistent(l_Lake_Toml_val);
    l_Lake_Toml_array = _init_l_Lake_Toml_array();
    leanh::lean_mark_persistent(l_Lake_Toml_array);
    l_Lake_Toml_inlineTable = _init_l_Lake_Toml_inlineTable();
    leanh::lean_mark_persistent(l_Lake_Toml_inlineTable);
    l_Lake_Toml_keyval = _init_l_Lake_Toml_keyval();
    leanh::lean_mark_persistent(l_Lake_Toml_keyval);
    l_Lake_Toml_expression = _init_l_Lake_Toml_expression();
    leanh::lean_mark_persistent(l_Lake_Toml_expression);
    l_Lake_Toml_key_formatter___closed__0___boxed__const__1 =
        _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(l_Lake_Toml_key_formatter___closed__0___boxed__const__1);
    l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1);
    l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1 =
        _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(
        l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1,
    );
    l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1 =
        _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1();
    leanh::lean_mark_persistent(
        l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1,
    );
    l_Lake_Toml_toml = _init_l_Lake_Toml_toml();
    leanh::lean_mark_persistent(l_Lake_Toml_toml);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Grammar(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Grammar(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Toml_ParserUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Formatter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Grammar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Grammar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Toml_Grammar(builtin);
}