// Lean compiler output
// Module: Lake.Toml.Grammar
// Imports: Lake.Toml.ParserUtil Lean.Parser Lean.PrettyPrinter.Formatter Lean.PrettyPrinter.Parenthesizer
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Syntax_isOfKind};
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
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_box_uint32, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_uint32,
    lean_unsigned_to_nat,
};
pub static l_Lake_Toml_wsFn___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_wsFn___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_wsFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_wsFn___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0_value:
    LeanStringObject<32> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_newlineFn___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_newlineFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_newlineFn___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_newlineFn___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_newlineFn___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_newlineFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_newlineFn___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_isControlChar___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_commentFn___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_commentFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_commentFn___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_commentFn___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_commentFn___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_commentFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_commentFn___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value:
    LeanStringObject<16> = LeanStringObject {
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
        101, 115, 99, 97, 112, 101, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3_value:
    LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_wsNewlineFn___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0_value
) as *mut LeanObject;
pub static l_Lake_Toml_basicStringFn___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_basicStringFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_basicStringFn___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_basicStringFn___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_basicStringFn___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_basicStringFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_basicStringFn___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0_value
) as *mut LeanObject;
pub static l_Lake_Toml_literalStringFn___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        108, 105, 116, 101, 114, 97, 108, 32, 115, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lake_Toml_literalStringFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_literalStringFn___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_literalStringFn___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_literalStringFn___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_literalStringFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_literalStringFn___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0_value:
    LeanStringObject<16> = LeanStringObject {
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
        116, 111, 111, 32, 109, 97, 110, 121, 32, 113, 117, 111, 116, 101, 115, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1_value:
    LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [109, 117, 108, 116, 105, 45, 108, 105, 110, 101, 32, 108, 105, 116, 101, 114, 97, 108, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_mlLiteralStringFn___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Lake_Toml_mlLiteralStringFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((3 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_Toml_mlLiteralStringFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlLiteralStringFn___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0_value:
    LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [109, 117, 108, 116, 105, 45, 108, 105, 110, 101, 32, 98, 97, 115, 105, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_mlBasicStringFn___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Lake_Toml_mlBasicStringFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((3 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_Toml_mlBasicStringFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlBasicStringFn___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3_value)
        as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0_value:
    LeanStringObject<30> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_Toml_timeFn___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_timeFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_timeFn___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_timeFn___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_timeFn___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_timeFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_timeFn___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1_value)
        as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [121, 101, 97, 114, 32, 100, 105, 103, 105, 116, 0]};
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value: LeanStringObject<
    17,
> = LeanStringObject {
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
        100, 101, 99, 105, 109, 97, 108, 32, 101, 120, 112, 111, 110, 101, 110, 116, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value
) as *mut LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value
        ) as *mut LeanObject,
        17795691646878718568 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_skipFn___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value
) as *mut LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value
        ) as *mut LeanObject,
        7221221276125824402 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value:
    LeanStringObject<17> = LeanStringObject {
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
        100, 101, 99, 105, 109, 97, 108, 32, 102, 114, 97, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8_value
) as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value:
    LeanStringObject<16> = LeanStringObject {
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
        100, 101, 99, 105, 109, 97, 108, 32, 105, 110, 116, 101, 103, 101, 114, 0,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value
)
    as *mut LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value
        ) as *mut LeanObject,
        14620934732133821028 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value
)
    as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value
)
    as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5_value
)
    as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__0_value: LeanStringObject<8> =
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
        m_data: [105, 110, 116, 101, 103, 101, 114, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_numeralFn___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__2_value: LeanStringObject<13> =
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
        m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_isHexDigit___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__4_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Toml_numeralFn___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__4_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_numeralFn___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__6_value: LeanStringObject<7> =
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
        m_data: [104, 101, 120, 78, 117, 109, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__6_value) as *mut LeanObject;
static l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_numeralFn___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__6_value) as *mut LeanObject,
        18206715719635152477 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_numeralFn___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_isOctDigit___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__8_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__9_value: LeanStringObject<14> =
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
            111, 99, 116, 97, 108, 32, 105, 110, 116, 101, 103, 101, 114, 0,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__9_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__9_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_numeralFn___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__10_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__11_value: LeanStringObject<7> =
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
        m_data: [111, 99, 116, 78, 117, 109, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__11_value) as *mut LeanObject;
static l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut LeanObject,
            13012506173997729135 as *mut LeanObject,
        ],
    };
static l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut LeanObject,
            16525079986463702690 as *mut LeanObject,
        ],
    };
pub static l_Lake_Toml_numeralFn___lam__0___closed__12_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__11_value) as *mut LeanObject,
        14236009889605174877 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_numeralFn___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__12_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__13_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_isBinDigit___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__13_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__14_value: LeanStringObject<15> =
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
            98, 105, 110, 97, 114, 121, 32, 105, 110, 116, 101, 103, 101, 114, 0,
        ],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__14_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__15_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__14_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_numeralFn___lam__0___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__15_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___lam__0___closed__16_value: LeanStringObject<7> =
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
        m_data: [98, 105, 110, 78, 117, 109, 0],
    };
static mut l_Lake_Toml_numeralFn___lam__0___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__16_value) as *mut LeanObject;
static l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
            ) as *mut LeanObject,
            13012506173997729135 as *mut LeanObject,
        ],
    };
static l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
            ) as *mut LeanObject,
            16525079986463702690 as *mut LeanObject,
        ],
    };
pub static l_Lake_Toml_numeralFn___lam__0___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__16_value) as *mut LeanObject,
        486821199203679291 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_numeralFn___lam__0___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___lam__0___closed__17_value) as *mut LeanObject;
pub static l_Lake_Toml_numeralFn___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_numeralFn___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_numeralFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralFn___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_trailingWs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_trailingWs___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_trailingWs: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_trailingSep___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_trailingFn___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_trailingSep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_trailingSep___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_trailingSep___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_trailingSep___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_trailingSep: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_unquotedKeyFn___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_unquotedKeyFn___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_unquotedKeyFn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKeyFn___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_unquotedKeyFn___closed__1_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_unquotedKeyFn___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKeyFn___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_unquotedKeyFn___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_unquotedKeyFn___closed__1_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_unquotedKeyFn___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKeyFn___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_unquotedKey___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_unquotedKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_unquotedKey___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_unquotedKey___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_unquotedKey___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__0_value) as *mut LeanObject,
        17377064587868252984 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_unquotedKey___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_unquotedKey___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_unquotedKey___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_unquotedKey___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_unquotedKey: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_basicString___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_basicString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_basicString___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_basicString___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_basicString___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_basicString___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_basicString___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_basicString___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_basicString___closed__0_value) as *mut LeanObject,
        16849499249217381028 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_basicString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_basicString___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_basicString___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_basicString___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_basicString: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_literalString___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        108, 105, 116, 101, 114, 97, 108, 83, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lake_Toml_literalString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_literalString___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_literalString___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_literalString___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_literalString___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_literalString___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_literalString___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_literalString___closed__0_value) as *mut LeanObject,
        6024408818386315505 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_literalString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_literalString___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_literalString___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_literalString___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_literalString: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_mlBasicString___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        109, 108, 66, 97, 115, 105, 99, 83, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lake_Toml_mlBasicString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_mlBasicString___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_mlBasicString___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_mlBasicString___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__0_value) as *mut LeanObject,
        1863697331681762253 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_mlBasicString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlBasicString___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_mlBasicString___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_mlBasicString___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_mlBasicString: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_mlLiteralString___closed__0_value: LeanStringObject<16> = LeanStringObject {
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
        109, 108, 76, 105, 116, 101, 114, 97, 108, 83, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lake_Toml_mlLiteralString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_mlLiteralString___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_mlLiteralString___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_mlLiteralString___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__0_value) as *mut LeanObject,
        3891709539368753145 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_mlLiteralString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mlLiteralString___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_mlLiteralString___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_mlLiteralString___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_mlLiteralString: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_quotedKey___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_quotedKey___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_quotedKey: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_simpleKey___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_simpleKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_simpleKey___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_simpleKey___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_simpleKey___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__0_value) as *mut LeanObject,
        15900767148364346299 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_simpleKey___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_simpleKey___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_simpleKey___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_simpleKey___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_simpleKey___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_simpleKey___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_simpleKey: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_key___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_key___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_key___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_key___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_key___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_key___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_key___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_key___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_key___closed__0_value) as *mut LeanObject,
        3865642880800790572 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_key___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_key___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_key___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_key___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_key___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_key___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_key___closed__3_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_key___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_key___closed__3_value) as *mut LeanObject;
static mut l_Lake_Toml_key___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_key: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_stdTable___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_stdTable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_stdTable___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_stdTable___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_stdTable___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__0_value) as *mut LeanObject,
        14174431292734320076 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_stdTable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_stdTable___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_stdTable___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_stdTable___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__2_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_stdTable___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__3_value) as *mut LeanObject;
static mut l_Lake_Toml_stdTable___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_stdTable___closed__10_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_stdTable___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_stdTable___closed__10_value) as *mut LeanObject;
static mut l_Lake_Toml_stdTable___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_stdTable: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_arrayTable___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_arrayTable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_arrayTable___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_arrayTable___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_arrayTable___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__0_value) as *mut LeanObject,
        1392117589206424775 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_arrayTable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_arrayTable___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_arrayTable___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_arrayTable: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_table___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_table___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_table: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value)
        as *mut LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value: LeanCtorObject<
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value)
            as *mut LeanObject,
        1860500813421358697 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value)
        as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value)
        as *mut LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value
        ) as *mut LeanObject,
        17299278796779604842 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value)
        as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Toml_header___closed__0_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Lake_Toml_header___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_header___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_header___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_header___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_header___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_header___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_header___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_header___closed__0_value) as *mut LeanObject,
        808944059858752425 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_header___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_header___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_header___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_header___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_header: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value: LeanStringObject<
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
    m_data: [116, 111, 109, 108, 0],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value)
        as *mut LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_1: LeanCtorObject<
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value: LeanCtorObject<
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value)
            as *mut LeanObject,
        4437657283425758961 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value: LeanStringObject<
    6,
> = LeanStringObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3_value: LeanCtorObject<
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
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value)
            as *mut LeanObject,
        10608024464111057092 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4_value: LeanStringObject<
    2,
> = LeanStringObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4_value)
        as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6_value: LeanStringObject<
    11,
> = LeanStringObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6_value)
        as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value
)
    as *mut LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value
        ) as *mut LeanObject,
        1671555236049616288 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3_value
)
    as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5_value:
    LeanStringObject<2> = LeanStringObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5_value
)
    as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value)
        as *mut LeanObject;
static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value: LeanCtorObject<
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
            l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value)
            as *mut LeanObject,
        9671799119587300413 as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2_value)
        as *mut LeanObject;
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Toml_string___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_string___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_string___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_string___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_string___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_string___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_string___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_string___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_string___closed__0_value) as *mut LeanObject,
        14667688617378285135 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_string___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_string___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_string___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_string___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_string___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_string___closed__2_value) as *mut LeanObject;
static mut l_Lake_Toml_string___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_string___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_string___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_string___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_string___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_string___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_string___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_string___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_string___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_string___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_string: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_true___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_true___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_true___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_true___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_true___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_true___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_true___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_true___closed__0_value) as *mut LeanObject,
        5919785301382904414 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_true___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_true___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_true___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_true___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_true___closed__2_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_true___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__3_value) as *mut LeanObject;
pub static l_Lake_Toml_true___closed__4_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_strFn as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_true___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_true___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_true___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_true___closed__4_value) as *mut LeanObject;
static mut l_Lake_Toml_true___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_true___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_true: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_false___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_false___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_false___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_false___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_false___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_false___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_false___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_false___closed__0_value) as *mut LeanObject,
        4008786854061235757 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_false___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_false___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_false___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_false___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_false___closed__2_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_false___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__3_value) as *mut LeanObject;
pub static l_Lake_Toml_false___closed__4_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_strFn as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_false___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_false___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_false___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_false___closed__4_value) as *mut LeanObject;
static mut l_Lake_Toml_false___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_false___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_false: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_boolean___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_boolean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_boolean___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_boolean___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_boolean___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_boolean___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_boolean___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_boolean___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_boolean___closed__0_value) as *mut LeanObject,
        8637345244662348 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_boolean___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_boolean___closed__1_value) as *mut LeanObject;
static mut l_Lake_Toml_boolean___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_boolean___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_boolean___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_boolean___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_boolean: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_numeralAntiquot___closed__6_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_numeralAntiquot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__6_value) as *mut LeanObject;
static l_Lake_Toml_numeralAntiquot___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_numeralAntiquot___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__7_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_numeralAntiquot___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__7_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__6_value) as *mut LeanObject,
        2769446217552894055 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_numeralAntiquot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralAntiquot___closed__7_value) as *mut LeanObject;
static mut l_Lake_Toml_numeralAntiquot___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeralAntiquot___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeralAntiquot___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_numeralAntiquot: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeral___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeral___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_numeral___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_numeral___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_numeral: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_numeralOfKind___closed__0_value: LeanStringObject<21> = LeanStringObject {
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
        105, 108, 108, 101, 103, 97, 108, 32, 110, 117, 109, 101, 114, 97, 108, 32, 107, 105, 110,
        100, 0,
    ],
};
static mut l_Lake_Toml_numeralOfKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_numeralOfKind___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_float___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_float___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_float: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_decInt___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_decInt___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_decInt: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_binNum___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        98, 105, 110, 97, 114, 121, 32, 110, 117, 109, 98, 101, 114, 0,
    ],
};
static mut l_Lake_Toml_binNum___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_binNum___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_binNum___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_binNum___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_binNum: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_octNum___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_octNum___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_octNum___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_octNum___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_octNum___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_octNum: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_hexNum___closed__0_value: LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_hexNum___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_hexNum___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_hexNum___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_hexNum___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_hexNum: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_dateTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_dateTime___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_dateTime: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_val___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_val___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_val___closed__0_value) as *mut LeanObject;
static l_Lake_Toml_val___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value
        ) as *mut LeanObject,
        13012506173997729135 as *mut LeanObject,
    ],
};
static l_Lake_Toml_val___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_val___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value
        ) as *mut LeanObject,
        16525079986463702690 as *mut LeanObject,
    ],
};
pub static l_Lake_Toml_val___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_val___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_val___closed__0_value) as *mut LeanObject,
        16311065367698350545 as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_val___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_val___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_val___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_val___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_val___closed__2_value) as *mut LeanObject;
static mut l_Lake_Toml_val___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_val___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_val: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_array___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_array___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_array: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_inlineTable___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_inlineTable___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_inlineTable: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_keyval___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_keyval___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_keyval: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_expression___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_expression___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_expression: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_simpleKey_formatter___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_simpleKey_formatter___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_key_formatter___closed__0___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_formatter___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_formatter___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_formatter___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_formatter___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_formatter___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_formatter___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_formatter___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_formatter___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_formatter___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_formatter___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_formatter___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_formatter___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_formatter___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_formatter___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_formatter___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_formatter___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0_value:
    LeanClosureObject<4> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_mkAntiquot_formatter___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0_value
) as *mut LeanObject;
static mut l_Lake_Toml_simpleKey_parenthesizer___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_simpleKey_parenthesizer___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_parenthesizer___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_parenthesizer___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_parenthesizer___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_parenthesizer___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_key_parenthesizer___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_key_parenthesizer___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_stdTable_parenthesizer___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_stdTable_parenthesizer___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_arrayTable_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0_value: LeanClosureObject<4> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 4, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0_value
) as *mut LeanObject;
static mut l_Lake_Toml_toml___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_toml___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_toml___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_toml___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_toml: *mut LeanObject = core::ptr::null_mut();
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
pub unsafe fn l_Lake_Toml_isControlChar___boxed(mut v_c_2847_: *mut LeanObject) -> *mut LeanObject {
    let mut v_c_boxed_2848_: u32 = 0;
    let mut v_res_2849_: u8 = 0;
    let mut v_r_2850_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2848_ = lean_unbox_uint32(v_c_2847_);
    lean_dec(v_c_2847_);
    v_res_2849_ = l_Lake_Toml_isControlChar(v_c_boxed_2848_);
    v_r_2850_ = lean_box((v_res_2849_) as usize);
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
pub unsafe fn l_Lake_Toml_wsFn___lam__0___boxed(mut v_c_2856_: *mut LeanObject) -> *mut LeanObject {
    let mut v_c_boxed_2857_: u32 = 0;
    let mut v_res_2858_: u8 = 0;
    let mut v_r_2859_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2857_ = lean_unbox_uint32(v_c_2856_);
    lean_dec(v_c_2856_);
    v_res_2858_ = l_Lake_Toml_wsFn___lam__0(v_c_boxed_2857_);
    v_r_2859_ = lean_box((v_res_2858_) as usize);
    return v_r_2859_;
}
pub unsafe fn l_Lake_Toml_wsFn(
    mut v_a_2861_: *mut LeanObject,
    mut v_a_2862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    v___f_2863_ = l_Lake_Toml_wsFn___closed__0;
    v___x_2864_ = l_Lean_Parser_takeWhileFn(v___f_2863_, v_a_2861_, v_a_2862_);
    return v___x_2864_;
}
pub unsafe fn l_Lake_Toml_wsFn___boxed(
    mut v_a_2865_: *mut LeanObject,
    mut v_a_2866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2867_: *mut LeanObject = core::ptr::null_mut();
    v_res_2867_ = l_Lake_Toml_wsFn(v_a_2865_, v_a_2866_);
    lean_dec_ref(v_a_2865_);
    return v_res_2867_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
    mut v_c_2869_: *mut LeanObject,
    mut v_s_2870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errMsg_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: u8 = 0;
    v_toInputContext_2871_ = lean_ctor_get(v_c_2869_, 0);
    v_pos_2872_ = lean_ctor_get(v_s_2870_, 2);
    v_errMsg_2873_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0;
    v___x_2874_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2871_, v_pos_2872_);
    v___x_2875_ = 1;
    if v___x_2874_ == 0 {
        let mut v_inputString_2876_: *mut LeanObject = core::ptr::null_mut();
        let mut v_curr_2877_: u32 = 0;
        let mut v___x_2878_: u32 = 0;
        let mut v___x_2879_: u8 = 0;
        v_inputString_2876_ = lean_ctor_get(v_toInputContext_2871_, 0);
        v_curr_2877_ = lean_string_utf8_get_fast(v_inputString_2876_, v_pos_2872_);
        v___x_2878_ = 10;
        v___x_2879_ = lean_uint32_dec_eq(v_curr_2877_, v___x_2878_);
        if v___x_2879_ == 0 {
            let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
            v___x_2880_ = lean_box(0);
            v___x_2881_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                v_s_2870_,
                v_errMsg_2873_,
                v___x_2880_,
                v___x_2875_,
            );
            return v___x_2881_;
        } else {
            let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_pos_2872_);
            v___x_2882_ =
                l_Lean_Parser_ParserState_next_x27___redArg(v_s_2870_, v_c_2869_, v_pos_2872_);
            lean_dec(v_pos_2872_);
            return v___x_2882_;
        }
    } else {
        let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
        v___x_2883_ = lean_box(0);
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
    mut v_c_2885_: *mut LeanObject,
    mut v_s_2886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2887_: *mut LeanObject = core::ptr::null_mut();
    v_res_2887_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_2885_, v_s_2886_);
    lean_dec_ref(v_c_2885_);
    return v_res_2887_;
}
pub unsafe fn l_Lake_Toml_newlineFn(
    mut v_c_2892_: *mut LeanObject,
    mut v_s_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: u8 = 0;
    v_toInputContext_2894_ = lean_ctor_get(v_c_2892_, 0);
    v_pos_2895_ = lean_ctor_get(v_s_2893_, 2);
    v___x_2896_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2894_, v_pos_2895_);
    if v___x_2896_ == 0 {
        let mut v_inputString_2897_: *mut LeanObject = core::ptr::null_mut();
        let mut v_curr_2898_: u32 = 0;
        let mut v___x_2899_: u32 = 0;
        let mut v___x_2900_: u8 = 0;
        v_inputString_2897_ = lean_ctor_get(v_toInputContext_2894_, 0);
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
                let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_pos_2895_);
                v___x_2906_ =
                    l_Lean_Parser_ParserState_next_x27___redArg(v_s_2893_, v_c_2892_, v_pos_2895_);
                lean_dec(v_pos_2895_);
                v___x_2907_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_2892_, v___x_2906_);
                return v___x_2907_;
            }
        } else {
            let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_pos_2895_);
            v___x_2908_ =
                l_Lean_Parser_ParserState_next_x27___redArg(v_s_2893_, v_c_2892_, v_pos_2895_);
            lean_dec(v_pos_2895_);
            return v___x_2908_;
        }
    } else {
        let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
        v___x_2909_ = l_Lake_Toml_newlineFn___closed__1;
        v___x_2910_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2893_, v___x_2909_);
        return v___x_2910_;
    }
}
pub unsafe fn l_Lake_Toml_newlineFn___boxed(
    mut v_c_2911_: *mut LeanObject,
    mut v_s_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2913_: *mut LeanObject = core::ptr::null_mut();
    v_res_2913_ = l_Lake_Toml_newlineFn(v_c_2911_, v_s_2912_);
    lean_dec_ref(v_c_2911_);
    return v_res_2913_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(
    mut v_a_2915_: *mut LeanObject,
    mut v_a_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    v___x_2917_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0;
    v___x_2918_ = l_Lean_Parser_takeUntilFn(v___x_2917_, v_a_2915_, v_a_2916_);
    return v___x_2918_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___boxed(
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2921_: *mut LeanObject = core::ptr::null_mut();
    v_res_2921_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_2919_, v_a_2920_);
    lean_dec_ref(v_a_2919_);
    return v_res_2921_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
    mut v_x_2922_: *mut LeanObject,
    mut v_x_2923_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2922_) == 0 {
        if lean_obj_tag(v_x_2923_) == 0 {
            let mut v___x_2924_: u8 = 0;
            v___x_2924_ = 1;
            return v___x_2924_;
        } else {
            let mut v___x_2925_: u8 = 0;
            lean_dec_ref_known(v_x_2923_, 1);
            v___x_2925_ = 0;
            return v___x_2925_;
        }
    } else {
        if lean_obj_tag(v_x_2923_) == 0 {
            let mut v___x_2926_: u8 = 0;
            lean_dec_ref_known(v_x_2922_, 1);
            v___x_2926_ = 0;
            return v___x_2926_;
        } else {
            let mut v_val_2927_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_2928_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2929_: u8 = 0;
            v_val_2927_ = lean_ctor_get(v_x_2922_, 0);
            lean_inc(v_val_2927_);
            lean_dec_ref_known(v_x_2922_, 1);
            v_val_2928_ = lean_ctor_get(v_x_2923_, 0);
            lean_inc(v_val_2928_);
            lean_dec_ref_known(v_x_2923_, 1);
            v___x_2929_ = l_Lean_Parser_instBEqError_beq(v_val_2927_, v_val_2928_);
            return v___x_2929_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0___boxed(
    mut v_x_2930_: *mut LeanObject,
    mut v_x_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2932_: u8 = 0;
    let mut v_r_2933_: *mut LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_x_2930_, v_x_2931_);
    v_r_2933_ = lean_box((v_res_2932_) as usize);
    return v_r_2933_;
}
pub unsafe fn l_Lake_Toml_commentFn(
    mut v_a_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2940_: u32 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: u8 = 0;
    v___x_2940_ = 35;
    v___x_2941_ = l_Lake_Toml_commentFn___closed__1;
    v_s_2942_ = l_Lake_Toml_chFn(v___x_2940_, v___x_2941_, v_a_2938_, v_a_2939_);
    v_errorMsg_2943_ = lean_ctor_get(v_s_2942_, 4);
    lean_inc(v_errorMsg_2943_);
    v___x_2944_ = lean_box(0);
    v___x_2945_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_2943_, v___x_2944_);
    if v___x_2945_ == 0 {
        return v_s_2942_;
    } else {
        let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
        v___x_2946_ =
            l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_2938_, v_s_2942_);
        return v___x_2946_;
    }
}
pub unsafe fn l_Lake_Toml_commentFn___boxed(
    mut v_a_2947_: *mut LeanObject,
    mut v_a_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2949_: *mut LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_Lake_Toml_commentFn(v_a_2947_, v_a_2948_);
    lean_dec_ref(v_a_2947_);
    return v_res_2949_;
}
pub unsafe fn l_Lake_Toml_wsNewlineFn(
    mut v_c_2950_: *mut LeanObject,
    mut v_s_2951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v_inputString_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_2959_: u32 = 0;
    let mut v___y_2961_: u8 = 0;
    let mut v___x_2962_: u32 = 0;
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: u32 = 0;
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2972_: u32 = 0;
    let mut v___x_2973_: u8 = 0;
    let mut v___x_2974_: u32 = 0;
    let mut v___x_2975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_2952_ = lean_ctor_get(v_c_2950_, 0);
                v_pos_2953_ = lean_ctor_get(v_s_2951_, 2);
                v___x_2957_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2952_, v_pos_2953_);
                if v___x_2957_ == 0 {
                    v_inputString_2958_ = lean_ctor_get(v_toInputContext_2952_, 0);
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
                lean_dec(v_pos_2953_);
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
                            lean_inc(v_pos_2953_);
                            v___x_2966_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_2951_,
                                v_c_2950_,
                                v_pos_2953_,
                            );
                            lean_dec(v_pos_2953_);
                            v_s_2967_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
                                v_c_2950_,
                                v___x_2966_,
                            );
                            v_errorMsg_2968_ = lean_ctor_get(v_s_2967_, 4);
                            lean_inc(v_errorMsg_2968_);
                            v___x_2969_ = lean_box(0);
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
                        lean_inc(v_pos_2953_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc(v_pos_2953_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_wsNewlineFn___boxed(
    mut v_c_2976_: *mut LeanObject,
    mut v_s_2977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2978_: *mut LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lake_Toml_wsNewlineFn(v_c_2976_, v_s_2977_);
    lean_dec_ref(v_c_2976_);
    return v_res_2978_;
}
pub unsafe fn l_Lake_Toml_trailingFn(
    mut v_c_2979_: *mut LeanObject,
    mut v_s_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v_inputString_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_2988_: u32 = 0;
    let mut v___y_2990_: u8 = 0;
    let mut v___x_2991_: u32 = 0;
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: u32 = 0;
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: u32 = 0;
    let mut v___x_2996_: u8 = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: u8 = 0;
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3009_: u32 = 0;
    let mut v___x_3010_: u8 = 0;
    let mut v___x_3011_: u32 = 0;
    let mut v___x_3012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_2981_ = lean_ctor_get(v_c_2979_, 0);
                v_pos_2982_ = lean_ctor_get(v_s_2980_, 2);
                v___x_2986_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2981_, v_pos_2982_);
                if v___x_2986_ == 0 {
                    v_inputString_2987_ = lean_ctor_get(v_toInputContext_2981_, 0);
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
                lean_dec(v_pos_2982_);
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
                                lean_inc(v_pos_2982_);
                                v___x_2997_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_2980_,
                                    v_c_2979_,
                                    v_pos_2982_,
                                );
                                lean_dec(v_pos_2982_);
                                v_s_2998_ =
                                    l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(
                                        v_c_2979_,
                                        v___x_2997_,
                                    );
                                v_errorMsg_2999_ = lean_ctor_get(v_s_2998_, 4);
                                lean_inc(v_errorMsg_2999_);
                                v___x_3000_ = lean_box(0);
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
                            lean_inc(v_pos_2982_);
                            v___x_3003_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_2980_,
                                v_c_2979_,
                                v_pos_2982_,
                            );
                            lean_dec(v_pos_2982_);
                            v_s_3004_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
                                v_c_2979_,
                                v___x_3003_,
                            );
                            v_errorMsg_3005_ = lean_ctor_get(v_s_3004_, 4);
                            lean_inc(v_errorMsg_3005_);
                            v___x_3006_ = lean_box(0);
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
                        lean_inc(v_pos_2982_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc(v_pos_2982_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_trailingFn___boxed(
    mut v_c_3013_: *mut LeanObject,
    mut v_s_3014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3015_: *mut LeanObject = core::ptr::null_mut();
    v_res_3015_ = l_Lake_Toml_trailingFn(v_c_3013_, v_s_3014_);
    lean_dec_ref(v_c_3013_);
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
pub unsafe fn l_Lake_Toml_isEscapeChar___boxed(mut v_c_3033_: *mut LeanObject) -> *mut LeanObject {
    let mut v_c_boxed_3034_: u32 = 0;
    let mut v_res_3035_: u8 = 0;
    let mut v_r_3036_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_3034_ = lean_unbox_uint32(v_c_3033_);
    lean_dec(v_c_3033_);
    v_res_3035_ = l_Lake_Toml_isEscapeChar(v_c_boxed_3034_);
    v_r_3036_ = lean_box((v_res_3035_) as usize);
    return v_r_3036_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(
    mut v___y_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    v_s_3039_ = l_Lake_Toml_wsFn(v___y_3037_, v___y_3038_);
    v_errorMsg_3040_ = lean_ctor_get(v_s_3039_, 4);
    lean_inc(v_errorMsg_3040_);
    v___x_3041_ = lean_box(0);
    v___x_3042_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3040_, v___x_3041_);
    if v___x_3042_ == 0 {
        return v_s_3039_;
    } else {
        let mut v_s_3043_: *mut LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3045_: u8 = 0;
        v_s_3043_ = l_Lake_Toml_newlineFn(v___y_3037_, v_s_3039_);
        v_errorMsg_3044_ = lean_ctor_get(v_s_3043_, 4);
        lean_inc(v_errorMsg_3044_);
        v___x_3045_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3044_,
            v___x_3041_,
        );
        if v___x_3045_ == 0 {
            return v_s_3043_;
        } else {
            let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
            v___x_3046_ = l_Lake_Toml_wsNewlineFn(v___y_3037_, v_s_3043_);
            return v___x_3046_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(
    mut v___y_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3049_: *mut LeanObject = core::ptr::null_mut();
    v_res_3049_ =
        l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(v___y_3047_, v___y_3048_);
    lean_dec_ref(v___y_3047_);
    return v_res_3049_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(
    mut v___y_3050_: *mut LeanObject,
    mut v___y_3051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u8 = 0;
    v_s_3052_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v___y_3050_, v___y_3051_);
    v_errorMsg_3053_ = lean_ctor_get(v_s_3052_, 4);
    lean_inc(v_errorMsg_3053_);
    v___x_3054_ = lean_box(0);
    v___x_3055_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3053_, v___x_3054_);
    if v___x_3055_ == 0 {
        return v_s_3052_;
    } else {
        let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
        v___x_3056_ = l_Lake_Toml_wsNewlineFn(v___y_3050_, v_s_3052_);
        return v___x_3056_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(
    mut v___y_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3059_: *mut LeanObject = core::ptr::null_mut();
    v_res_3059_ =
        l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(v___y_3057_, v___y_3058_);
    lean_dec_ref(v___y_3057_);
    return v_res_3059_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(
    mut v_c_3060_: *mut LeanObject,
    mut v_x_3061_: *mut LeanObject,
    mut v_x_3062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3064_: u8 = 0;
    let mut v_s_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v_one_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3063_ = lean_unsigned_to_nat(0);
                v_isZero_3064_ = lean_nat_dec_eq(v_x_3061_, v_zero_3063_);
                if v_isZero_3064_ == 1 {
                    lean_dec(v_x_3061_);
                    return v_x_3062_;
                } else {
                    v_s_3065_ = l_Lean_Parser_hexDigitFn(v_c_3060_, v_x_3062_);
                    v_errorMsg_3066_ = lean_ctor_get(v_s_3065_, 4);
                    lean_inc(v_errorMsg_3066_);
                    v___x_3067_ = lean_box(0);
                    v___x_3068_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3066_,
                        v___x_3067_,
                    );
                    if v___x_3068_ == 0 {
                        lean_dec(v_x_3061_);
                        return v_s_3065_;
                    } else {
                        v_one_3069_ = lean_unsigned_to_nat(1);
                        v_n_3070_ = lean_nat_sub(v_x_3061_, v_one_3069_);
                        lean_dec(v_x_3061_);
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
    mut v_c_3072_: *mut LeanObject,
    mut v_x_3073_: *mut LeanObject,
    mut v_x_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3075_: *mut LeanObject = core::ptr::null_mut();
    v_res_3075_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_3072_, v_x_3073_, v_x_3074_);
    lean_dec_ref(v_c_3072_);
    return v_res_3075_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(
    mut v_stringGap_3085_: u8,
    mut v_c_3086_: *mut LeanObject,
    mut v_s_3087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: u8 = 0;
    let mut v_inputString_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3094_: u32 = 0;
    let mut v___x_3095_: u8 = 0;
    let mut v___x_3096_: u32 = 0;
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: u32 = 0;
    let mut v___x_3099_: u8 = 0;
    let mut v___f_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v_p_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u32 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: u32 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: u32 = 0;
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: u32 = 0;
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3088_ = lean_ctor_get(v_c_3086_, 0);
                v_pos_3089_ = lean_ctor_get(v_s_3087_, 2);
                v___x_3090_ = lean_box(0);
                v_expected_3091_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1;
                v___x_3092_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3088_, v_pos_3089_);
                if v___x_3092_ == 0 {
                    v_inputString_3093_ = lean_ctor_get(v_toInputContext_3088_, 0);
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
                                                lean_dec_ref(v_c_3086_);
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
                                lean_inc(v_pos_3089_);
                                v___x_3120_ = lean_unsigned_to_nat(8);
                                v___x_3121_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_3087_,
                                    v_c_3086_,
                                    v_pos_3089_,
                                );
                                lean_dec(v_pos_3089_);
                                v___x_3122_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_3086_, v___x_3120_, v___x_3121_);
                                lean_dec_ref(v_c_3086_);
                                return v___x_3122_;
                            }
                        } else {
                            lean_inc(v_pos_3089_);
                            v___x_3123_ = lean_unsigned_to_nat(4);
                            v___x_3124_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_3087_,
                                v_c_3086_,
                                v_pos_3089_,
                            );
                            lean_dec(v_pos_3089_);
                            v___x_3125_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_3086_, v___x_3123_, v___x_3124_);
                            lean_dec_ref(v_c_3086_);
                            return v___x_3125_;
                        }
                    } else {
                        lean_inc(v_pos_3089_);
                        v___x_3126_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3087_,
                            v_c_3086_,
                            v_pos_3089_,
                        );
                        lean_dec(v_pos_3089_);
                        lean_dec_ref(v_c_3086_);
                        return v___x_3126_;
                    }
                } else {
                    lean_dec_ref(v_c_3086_);
                    v___x_3127_ = l_Lean_Parser_ParserState_mkEOIError(v_s_3087_, v_expected_3091_);
                    return v___x_3127_;
                }
            }
            1 => {
                if v_stringGap_3085_ == 0 {
                    lean_dec_ref(v_c_3086_);
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
                    lean_inc(v_pos_3089_);
                    v___x_3106_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3087_,
                        v_c_3086_,
                        v_pos_3089_,
                    );
                    lean_dec(v_pos_3089_);
                    lean_inc_ref(v_p_3103_);
                    v___x_3107_ = lean_apply_2(v_p_3103_, v_c_3086_, v___x_3106_);
                    return v___x_3107_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(
    mut v_stringGap_3128_: *mut LeanObject,
    mut v_c_3129_: *mut LeanObject,
    mut v_s_3130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stringGap_boxed_3131_: u8 = 0;
    let mut v_res_3132_: *mut LeanObject = core::ptr::null_mut();
    v_stringGap_boxed_3131_ = (lean_unbox(v_stringGap_3128_) as u8);
    v_res_3132_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(
        v_stringGap_boxed_3131_,
        v_c_3129_,
        v_s_3130_,
    );
    return v_res_3132_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(
    mut v_startPos_3134_: *mut LeanObject,
    mut v_c_3135_: *mut LeanObject,
    mut v_s_3136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v_inputString_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3141_: u32 = 0;
    let mut v___x_3142_: u32 = 0;
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: u32 = 0;
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: u8 = 0;
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: u8 = 0;
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3137_ = lean_ctor_get(v_c_3135_, 0);
                v_pos_3138_ = lean_ctor_get(v_s_3136_, 2);
                v___x_3139_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3137_, v_pos_3138_);
                if v___x_3139_ == 0 {
                    v_inputString_3140_ = lean_ctor_get(v_toInputContext_3137_, 0);
                    v_curr_3141_ = lean_string_utf8_get_fast(v_inputString_3140_, v_pos_3138_);
                    v___x_3142_ = 34;
                    v___x_3143_ = lean_uint32_dec_eq(v_curr_3141_, v___x_3142_);
                    if v___x_3143_ == 0 {
                        v___x_3144_ = 92;
                        v___x_3145_ = lean_uint32_dec_eq(v_curr_3141_, v___x_3144_);
                        if v___x_3145_ == 0 {
                            v___x_3146_ = l_Lake_Toml_isControlChar(v_curr_3141_);
                            if v___x_3146_ == 0 {
                                lean_inc(v_pos_3138_);
                                v___x_3147_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_3136_,
                                    v_c_3135_,
                                    v_pos_3138_,
                                );
                                lean_dec(v_pos_3138_);
                                v_s_3136_ = v___x_3147_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec_ref(v_c_3135_);
                                lean_dec(v_startPos_3134_);
                                v___x_3149_ = lean_box(0);
                                v___x_3150_ = l_Lake_Toml_mkUnexpectedCharError(
                                    v_s_3136_,
                                    v_curr_3141_,
                                    v___x_3149_,
                                    v___x_3146_,
                                );
                                return v___x_3150_;
                            }
                        } else {
                            lean_inc(v_pos_3138_);
                            v___x_3151_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_3136_,
                                v_c_3135_,
                                v_pos_3138_,
                            );
                            lean_dec(v_pos_3138_);
                            lean_inc_ref(v_c_3135_);
                            v_s_3152_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(
                                v___x_3143_,
                                v_c_3135_,
                                v___x_3151_,
                            );
                            v_errorMsg_3153_ = lean_ctor_get(v_s_3152_, 4);
                            lean_inc(v_errorMsg_3153_);
                            v___x_3154_ = lean_box(0);
                            v___x_3155_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                v_errorMsg_3153_,
                                v___x_3154_,
                            );
                            if v___x_3155_ == 0 {
                                lean_dec_ref(v_c_3135_);
                                lean_dec(v_startPos_3134_);
                                return v_s_3152_;
                            } else {
                                v_s_3136_ = v_s_3152_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        lean_inc(v_pos_3138_);
                        lean_dec(v_startPos_3134_);
                        v___x_3157_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3136_,
                            v_c_3135_,
                            v_pos_3138_,
                        );
                        lean_dec(v_pos_3138_);
                        lean_dec_ref(v_c_3135_);
                        return v___x_3157_;
                    }
                } else {
                    lean_dec_ref(v_c_3135_);
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
    mut v_a_3164_: *mut LeanObject,
    mut v_a_3165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: u32 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    v_pos_3166_ = lean_ctor_get(v_a_3165_, 2);
    lean_inc(v_pos_3166_);
    v___x_3167_ = 34;
    v___x_3168_ = l_Lake_Toml_basicStringFn___closed__1;
    v_s_3169_ = l_Lake_Toml_chFn(v___x_3167_, v___x_3168_, v_a_3164_, v_a_3165_);
    v_errorMsg_3170_ = lean_ctor_get(v_s_3169_, 4);
    lean_inc(v_errorMsg_3170_);
    v___x_3171_ = lean_box(0);
    v___x_3172_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3170_, v___x_3171_);
    if v___x_3172_ == 0 {
        lean_dec(v_pos_3166_);
        lean_dec_ref(v_a_3164_);
        return v_s_3169_;
    } else {
        let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
        v___x_3173_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(
            v_pos_3166_,
            v_a_3164_,
            v_s_3169_,
        );
        return v___x_3173_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(
    mut v_startPos_3175_: *mut LeanObject,
    mut v_c_3176_: *mut LeanObject,
    mut v_s_3177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: u8 = 0;
    let mut v_inputString_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3182_: u32 = 0;
    let mut v___x_3183_: u32 = 0;
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: u8 = 0;
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3178_ = lean_ctor_get(v_c_3176_, 0);
                v_pos_3179_ = lean_ctor_get(v_s_3177_, 2);
                v___x_3180_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3178_, v_pos_3179_);
                if v___x_3180_ == 0 {
                    v_inputString_3181_ = lean_ctor_get(v_toInputContext_3178_, 0);
                    v_curr_3182_ = lean_string_utf8_get_fast(v_inputString_3181_, v_pos_3179_);
                    v___x_3183_ = 39;
                    v___x_3184_ = lean_uint32_dec_eq(v_curr_3182_, v___x_3183_);
                    if v___x_3184_ == 0 {
                        v___x_3185_ = l_Lake_Toml_isControlChar(v_curr_3182_);
                        if v___x_3185_ == 0 {
                            lean_inc(v_pos_3179_);
                            v___x_3186_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_3177_,
                                v_c_3176_,
                                v_pos_3179_,
                            );
                            lean_dec(v_pos_3179_);
                            v_s_3177_ = v___x_3186_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_startPos_3175_);
                            v___x_3188_ = lean_box(0);
                            v___x_3189_ = l_Lake_Toml_mkUnexpectedCharError(
                                v_s_3177_,
                                v_curr_3182_,
                                v___x_3188_,
                                v___x_3185_,
                            );
                            return v___x_3189_;
                        }
                    } else {
                        lean_inc(v_pos_3179_);
                        lean_dec(v_startPos_3175_);
                        v___x_3190_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3177_,
                            v_c_3176_,
                            v_pos_3179_,
                        );
                        lean_dec(v_pos_3179_);
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
    mut v_startPos_3193_: *mut LeanObject,
    mut v_c_3194_: *mut LeanObject,
    mut v_s_3195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3196_: *mut LeanObject = core::ptr::null_mut();
    v_res_3196_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(
        v_startPos_3193_,
        v_c_3194_,
        v_s_3195_,
    );
    lean_dec_ref(v_c_3194_);
    return v_res_3196_;
}
pub unsafe fn l_Lake_Toml_literalStringFn(
    mut v_a_3201_: *mut LeanObject,
    mut v_a_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u32 = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    v_pos_3203_ = lean_ctor_get(v_a_3202_, 2);
    lean_inc(v_pos_3203_);
    v___x_3204_ = 39;
    v___x_3205_ = l_Lake_Toml_literalStringFn___closed__1;
    v_s_3206_ = l_Lake_Toml_chFn(v___x_3204_, v___x_3205_, v_a_3201_, v_a_3202_);
    v_errorMsg_3207_ = lean_ctor_get(v_s_3206_, 4);
    lean_inc(v_errorMsg_3207_);
    v___x_3208_ = lean_box(0);
    v___x_3209_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3207_, v___x_3208_);
    if v___x_3209_ == 0 {
        lean_dec(v_pos_3203_);
        return v_s_3206_;
    } else {
        let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
        v___x_3210_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(
            v_pos_3203_,
            v_a_3201_,
            v_s_3206_,
        );
        return v___x_3210_;
    }
}
pub unsafe fn l_Lake_Toml_literalStringFn___boxed(
    mut v_a_3211_: *mut LeanObject,
    mut v_a_3212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3213_: *mut LeanObject = core::ptr::null_mut();
    v_res_3213_ = l_Lake_Toml_literalStringFn(v_a_3211_, v_a_3212_);
    lean_dec_ref(v_a_3211_);
    return v_res_3213_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(
    mut v_startPos_3216_: *mut LeanObject,
    mut v_quoteDepth_3217_: *mut LeanObject,
    mut v_c_3218_: *mut LeanObject,
    mut v_s_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: u8 = 0;
    let mut v_inputString_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u8 = 0;
    let mut v_curr_3225_: u32 = 0;
    let mut v___x_3226_: u32 = 0;
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3230_: u32 = 0;
    let mut v___x_3231_: u8 = 0;
    let mut v___x_3232_: u32 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3220_ = lean_ctor_get(v_c_3218_, 0);
                v_pos_3221_ = lean_ctor_get(v_s_3219_, 2);
                v___x_3222_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3220_, v_pos_3221_);
                if v___x_3222_ == 0 {
                    v_inputString_3223_ = lean_ctor_get(v_toInputContext_3220_, 0);
                    v___x_3224_ = 1;
                    v_curr_3225_ = lean_string_utf8_get_fast(v_inputString_3223_, v_pos_3221_);
                    v___x_3226_ = 39;
                    v___x_3227_ = lean_uint32_dec_eq(v_curr_3225_, v___x_3226_);
                    if v___x_3227_ == 0 {
                        v___x_3228_ = lean_unsigned_to_nat(3);
                        v___x_3229_ = lean_nat_dec_le(v___x_3228_, v_quoteDepth_3217_);
                        lean_dec(v_quoteDepth_3217_);
                        if v___x_3229_ == 0 {
                            v___x_3230_ = 10;
                            v___x_3231_ = lean_uint32_dec_eq(v_curr_3225_, v___x_3230_);
                            if v___x_3231_ == 0 {
                                v___x_3232_ = 13;
                                v___x_3233_ = lean_uint32_dec_eq(v_curr_3225_, v___x_3232_);
                                if v___x_3233_ == 0 {
                                    v___x_3234_ = l_Lake_Toml_isControlChar(v_curr_3225_);
                                    if v___x_3234_ == 0 {
                                        lean_inc(v_pos_3221_);
                                        v___x_3235_ = lean_unsigned_to_nat(0);
                                        v___x_3236_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                            v_s_3219_,
                                            v_c_3218_,
                                            v_pos_3221_,
                                        );
                                        lean_dec(v_pos_3221_);
                                        v_quoteDepth_3217_ = v___x_3235_;
                                        v_s_3219_ = v___x_3236_;
                                        state = 0;
                                        continue;
                                    } else {
                                        lean_dec(v_startPos_3216_);
                                        v___x_3238_ = lean_box(0);
                                        v___x_3239_ = l_Lake_Toml_mkUnexpectedCharError(
                                            v_s_3219_,
                                            v_curr_3225_,
                                            v___x_3238_,
                                            v___x_3224_,
                                        );
                                        return v___x_3239_;
                                    }
                                } else {
                                    lean_inc(v_pos_3221_);
                                    v___x_3240_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                        v_s_3219_,
                                        v_c_3218_,
                                        v_pos_3221_,
                                    );
                                    lean_dec(v_pos_3221_);
                                    v_s_3241_ =
                                        l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
                                            v_c_3218_,
                                            v___x_3240_,
                                        );
                                    v_errorMsg_3242_ = lean_ctor_get(v_s_3241_, 4);
                                    lean_inc(v_errorMsg_3242_);
                                    v___x_3243_ = lean_box(0);
                                    v___x_3244_ =
                                        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                            v_errorMsg_3242_,
                                            v___x_3243_,
                                        );
                                    if v___x_3244_ == 0 {
                                        lean_dec(v_startPos_3216_);
                                        return v_s_3241_;
                                    } else {
                                        v___x_3245_ = lean_unsigned_to_nat(0);
                                        v_quoteDepth_3217_ = v___x_3245_;
                                        v_s_3219_ = v_s_3241_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc(v_pos_3221_);
                                v___x_3247_ = lean_unsigned_to_nat(0);
                                v___x_3248_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_3219_,
                                    v_c_3218_,
                                    v_pos_3221_,
                                );
                                lean_dec(v_pos_3221_);
                                v_quoteDepth_3217_ = v___x_3247_;
                                v_s_3219_ = v___x_3248_;
                                state = 0;
                                continue;
                            }
                        } else {
                            lean_dec(v_startPos_3216_);
                            return v_s_3219_;
                        }
                    } else {
                        lean_inc(v_pos_3221_);
                        v_s_3250_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3219_,
                            v_c_3218_,
                            v_pos_3221_,
                        );
                        lean_dec(v_pos_3221_);
                        v___x_3251_ = lean_unsigned_to_nat(5);
                        v___x_3252_ = lean_nat_dec_le(v___x_3251_, v_quoteDepth_3217_);
                        if v___x_3252_ == 0 {
                            v___x_3253_ = lean_unsigned_to_nat(1);
                            v___x_3254_ = lean_nat_add(v_quoteDepth_3217_, v___x_3253_);
                            lean_dec(v_quoteDepth_3217_);
                            v_quoteDepth_3217_ = v___x_3254_;
                            v_s_3219_ = v_s_3250_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_quoteDepth_3217_);
                            lean_dec(v_startPos_3216_);
                            v___x_3256_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0;
                            v___x_3257_ = lean_box(0);
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
                    v___x_3259_ = lean_unsigned_to_nat(3);
                    v___x_3260_ = lean_nat_dec_le(v___x_3259_, v_quoteDepth_3217_);
                    lean_dec(v_quoteDepth_3217_);
                    if v___x_3260_ == 0 {
                        v___x_3261_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1;
                        v___x_3262_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(
                            v_s_3219_,
                            v___x_3261_,
                            v_startPos_3216_,
                        );
                        return v___x_3262_;
                    } else {
                        lean_dec(v_startPos_3216_);
                        return v_s_3219_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(
    mut v_startPos_3263_: *mut LeanObject,
    mut v_quoteDepth_3264_: *mut LeanObject,
    mut v_c_3265_: *mut LeanObject,
    mut v_s_3266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3267_: *mut LeanObject = core::ptr::null_mut();
    v_res_3267_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(
        v_startPos_3263_,
        v_quoteDepth_3264_,
        v_c_3265_,
        v_s_3266_,
    );
    lean_dec_ref(v_c_3265_);
    return v_res_3267_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(
    mut v_c_3272_: *mut LeanObject,
    mut v_x_3273_: *mut LeanObject,
    mut v_x_3274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3276_: u8 = 0;
    let mut v___x_3277_: u32 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v_one_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3275_ = lean_unsigned_to_nat(0);
                v_isZero_3276_ = lean_nat_dec_eq(v_x_3273_, v_zero_3275_);
                if v_isZero_3276_ == 1 {
                    lean_dec(v_x_3273_);
                    return v_x_3274_;
                } else {
                    v___x_3277_ = 39;
                    v___x_3278_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1;
                    v_s_3279_ = l_Lake_Toml_chFn(v___x_3277_, v___x_3278_, v_c_3272_, v_x_3274_);
                    v_errorMsg_3280_ = lean_ctor_get(v_s_3279_, 4);
                    lean_inc(v_errorMsg_3280_);
                    v___x_3281_ = lean_box(0);
                    v___x_3282_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3280_,
                        v___x_3281_,
                    );
                    if v___x_3282_ == 0 {
                        lean_dec(v_x_3273_);
                        return v_s_3279_;
                    } else {
                        v_one_3283_ = lean_unsigned_to_nat(1);
                        v_n_3284_ = lean_nat_sub(v_x_3273_, v_one_3283_);
                        lean_dec(v_x_3273_);
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
    mut v_c_3286_: *mut LeanObject,
    mut v_x_3287_: *mut LeanObject,
    mut v_x_3288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3289_: *mut LeanObject = core::ptr::null_mut();
    v_res_3289_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v_c_3286_, v_x_3287_, v_x_3288_);
    lean_dec_ref(v_c_3286_);
    return v_res_3289_;
}
pub unsafe fn l_Lake_Toml_mlLiteralStringFn___lam__0(
    mut v___x_3290_: *mut LeanObject,
    mut v___y_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    v___x_3293_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v___y_3291_, v___x_3290_, v___y_3292_);
    return v___x_3293_;
}
pub unsafe fn l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(
    mut v___x_3294_: *mut LeanObject,
    mut v___y_3295_: *mut LeanObject,
    mut v___y_3296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3297_: *mut LeanObject = core::ptr::null_mut();
    v_res_3297_ = l_Lake_Toml_mlLiteralStringFn___lam__0(v___x_3294_, v___y_3295_, v___y_3296_);
    lean_dec_ref(v___y_3295_);
    return v_res_3297_;
}
pub unsafe fn l_Lake_Toml_mlLiteralStringFn(
    mut v_a_3300_: *mut LeanObject,
    mut v_a_3301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    v_pos_3302_ = lean_ctor_get(v_a_3301_, 2);
    lean_inc(v_pos_3302_);
    v___f_3303_ = l_Lake_Toml_mlLiteralStringFn___closed__0;
    lean_inc_ref(v_a_3300_);
    v_s_3304_ = l_Lean_Parser_atomicFn(v___f_3303_, v_a_3300_, v_a_3301_);
    v_errorMsg_3305_ = lean_ctor_get(v_s_3304_, 4);
    lean_inc(v_errorMsg_3305_);
    v___x_3306_ = lean_box(0);
    v___x_3307_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3305_, v___x_3306_);
    if v___x_3307_ == 0 {
        lean_dec(v_pos_3302_);
        lean_dec_ref(v_a_3300_);
        return v_s_3304_;
    } else {
        let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
        v___x_3308_ = lean_unsigned_to_nat(0);
        v___x_3309_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(
            v_pos_3302_,
            v___x_3308_,
            v_a_3300_,
            v_s_3304_,
        );
        lean_dec_ref(v_a_3300_);
        return v___x_3309_;
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(
    mut v_startPos_3311_: *mut LeanObject,
    mut v_quoteDepth_3312_: *mut LeanObject,
    mut v_c_3313_: *mut LeanObject,
    mut v_s_3314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: u8 = 0;
    let mut v_inputString_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v_curr_3320_: u32 = 0;
    let mut v___x_3321_: u32 = 0;
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: u32 = 0;
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: u32 = 0;
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: u32 = 0;
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: u8 = 0;
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: u8 = 0;
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u8 = 0;
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3315_ = lean_ctor_get(v_c_3313_, 0);
                v_pos_3316_ = lean_ctor_get(v_s_3314_, 2);
                v___x_3317_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3315_, v_pos_3316_);
                if v___x_3317_ == 0 {
                    v_inputString_3318_ = lean_ctor_get(v_toInputContext_3315_, 0);
                    v___x_3319_ = 1;
                    v_curr_3320_ = lean_string_utf8_get_fast(v_inputString_3318_, v_pos_3316_);
                    v___x_3321_ = 34;
                    v___x_3322_ = lean_uint32_dec_eq(v_curr_3320_, v___x_3321_);
                    if v___x_3322_ == 0 {
                        v___x_3323_ = lean_unsigned_to_nat(3);
                        v___x_3324_ = lean_nat_dec_le(v___x_3323_, v_quoteDepth_3312_);
                        lean_dec(v_quoteDepth_3312_);
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
                                            lean_inc(v_pos_3316_);
                                            v___x_3332_ = lean_unsigned_to_nat(0);
                                            v___x_3333_ =
                                                l_Lean_Parser_ParserState_next_x27___redArg(
                                                    v_s_3314_,
                                                    v_c_3313_,
                                                    v_pos_3316_,
                                                );
                                            lean_dec(v_pos_3316_);
                                            v_quoteDepth_3312_ = v___x_3332_;
                                            v_s_3314_ = v___x_3333_;
                                            state = 0;
                                            continue;
                                        } else {
                                            lean_dec_ref(v_c_3313_);
                                            lean_dec(v_startPos_3311_);
                                            v___x_3335_ = lean_box(0);
                                            v___x_3336_ = l_Lake_Toml_mkUnexpectedCharError(
                                                v_s_3314_,
                                                v_curr_3320_,
                                                v___x_3335_,
                                                v___x_3319_,
                                            );
                                            return v___x_3336_;
                                        }
                                    } else {
                                        lean_inc(v_pos_3316_);
                                        v___x_3337_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                            v_s_3314_,
                                            v_c_3313_,
                                            v_pos_3316_,
                                        );
                                        lean_dec(v_pos_3316_);
                                        lean_inc_ref(v_c_3313_);
                                        v_s_3338_ =
                                            l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(
                                                v___x_3319_,
                                                v_c_3313_,
                                                v___x_3337_,
                                            );
                                        v_errorMsg_3339_ = lean_ctor_get(v_s_3338_, 4);
                                        lean_inc(v_errorMsg_3339_);
                                        v___x_3340_ = lean_box(0);
                                        v___x_3341_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3339_, v___x_3340_);
                                        if v___x_3341_ == 0 {
                                            lean_dec_ref(v_c_3313_);
                                            lean_dec(v_startPos_3311_);
                                            return v_s_3338_;
                                        } else {
                                            v___x_3342_ = lean_unsigned_to_nat(0);
                                            v_quoteDepth_3312_ = v___x_3342_;
                                            v_s_3314_ = v_s_3338_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_inc(v_pos_3316_);
                                    v___x_3344_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                        v_s_3314_,
                                        v_c_3313_,
                                        v_pos_3316_,
                                    );
                                    lean_dec(v_pos_3316_);
                                    v_s_3345_ =
                                        l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(
                                            v_c_3313_,
                                            v___x_3344_,
                                        );
                                    v_errorMsg_3346_ = lean_ctor_get(v_s_3345_, 4);
                                    lean_inc(v_errorMsg_3346_);
                                    v___x_3347_ = lean_box(0);
                                    v___x_3348_ =
                                        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                                            v_errorMsg_3346_,
                                            v___x_3347_,
                                        );
                                    if v___x_3348_ == 0 {
                                        lean_dec_ref(v_c_3313_);
                                        lean_dec(v_startPos_3311_);
                                        return v_s_3345_;
                                    } else {
                                        v___x_3349_ = lean_unsigned_to_nat(0);
                                        v_quoteDepth_3312_ = v___x_3349_;
                                        v_s_3314_ = v_s_3345_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc(v_pos_3316_);
                                v___x_3351_ = lean_unsigned_to_nat(0);
                                v___x_3352_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                    v_s_3314_,
                                    v_c_3313_,
                                    v_pos_3316_,
                                );
                                lean_dec(v_pos_3316_);
                                v_quoteDepth_3312_ = v___x_3351_;
                                v_s_3314_ = v___x_3352_;
                                state = 0;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_c_3313_);
                            lean_dec(v_startPos_3311_);
                            return v_s_3314_;
                        }
                    } else {
                        lean_inc(v_pos_3316_);
                        v_s_3354_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3314_,
                            v_c_3313_,
                            v_pos_3316_,
                        );
                        lean_dec(v_pos_3316_);
                        v___x_3355_ = lean_unsigned_to_nat(5);
                        v___x_3356_ = lean_nat_dec_le(v___x_3355_, v_quoteDepth_3312_);
                        if v___x_3356_ == 0 {
                            v___x_3357_ = lean_unsigned_to_nat(1);
                            v___x_3358_ = lean_nat_add(v_quoteDepth_3312_, v___x_3357_);
                            lean_dec(v_quoteDepth_3312_);
                            v_quoteDepth_3312_ = v___x_3358_;
                            v_s_3314_ = v_s_3354_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_c_3313_);
                            lean_dec(v_quoteDepth_3312_);
                            lean_dec(v_startPos_3311_);
                            v___x_3360_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0;
                            v___x_3361_ = lean_box(0);
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
                    lean_dec_ref(v_c_3313_);
                    v___x_3363_ = lean_unsigned_to_nat(3);
                    v___x_3364_ = lean_nat_dec_le(v___x_3363_, v_quoteDepth_3312_);
                    lean_dec(v_quoteDepth_3312_);
                    if v___x_3364_ == 0 {
                        v___x_3365_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0;
                        v___x_3366_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(
                            v_s_3314_,
                            v___x_3365_,
                            v_startPos_3311_,
                        );
                        return v___x_3366_;
                    } else {
                        lean_dec(v_startPos_3311_);
                        return v_s_3314_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(
    mut v_c_3371_: *mut LeanObject,
    mut v_x_3372_: *mut LeanObject,
    mut v_x_3373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3375_: u8 = 0;
    let mut v___x_3376_: u32 = 0;
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: u8 = 0;
    let mut v_one_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3374_ = lean_unsigned_to_nat(0);
                v_isZero_3375_ = lean_nat_dec_eq(v_x_3372_, v_zero_3374_);
                if v_isZero_3375_ == 1 {
                    lean_dec(v_x_3372_);
                    return v_x_3373_;
                } else {
                    v___x_3376_ = 34;
                    v___x_3377_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1;
                    v_s_3378_ = l_Lake_Toml_chFn(v___x_3376_, v___x_3377_, v_c_3371_, v_x_3373_);
                    v_errorMsg_3379_ = lean_ctor_get(v_s_3378_, 4);
                    lean_inc(v_errorMsg_3379_);
                    v___x_3380_ = lean_box(0);
                    v___x_3381_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3379_,
                        v___x_3380_,
                    );
                    if v___x_3381_ == 0 {
                        lean_dec(v_x_3372_);
                        return v_s_3378_;
                    } else {
                        v_one_3382_ = lean_unsigned_to_nat(1);
                        v_n_3383_ = lean_nat_sub(v_x_3372_, v_one_3382_);
                        lean_dec(v_x_3372_);
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
    mut v_c_3385_: *mut LeanObject,
    mut v_x_3386_: *mut LeanObject,
    mut v_x_3387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3388_: *mut LeanObject = core::ptr::null_mut();
    v_res_3388_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v_c_3385_, v_x_3386_, v_x_3387_);
    lean_dec_ref(v_c_3385_);
    return v_res_3388_;
}
pub unsafe fn l_Lake_Toml_mlBasicStringFn___lam__0(
    mut v___x_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    v___x_3392_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v___y_3390_, v___x_3389_, v___y_3391_);
    return v___x_3392_;
}
pub unsafe fn l_Lake_Toml_mlBasicStringFn___lam__0___boxed(
    mut v___x_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3396_: *mut LeanObject = core::ptr::null_mut();
    v_res_3396_ = l_Lake_Toml_mlBasicStringFn___lam__0(v___x_3393_, v___y_3394_, v___y_3395_);
    lean_dec_ref(v___y_3394_);
    return v_res_3396_;
}
pub unsafe fn l_Lake_Toml_mlBasicStringFn(
    mut v_a_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: u8 = 0;
    v_pos_3401_ = lean_ctor_get(v_a_3400_, 2);
    lean_inc(v_pos_3401_);
    v___f_3402_ = l_Lake_Toml_mlBasicStringFn___closed__0;
    lean_inc_ref(v_a_3399_);
    v_s_3403_ = l_Lean_Parser_atomicFn(v___f_3402_, v_a_3399_, v_a_3400_);
    v_errorMsg_3404_ = lean_ctor_get(v_s_3403_, 4);
    lean_inc(v_errorMsg_3404_);
    v___x_3405_ = lean_box(0);
    v___x_3406_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3404_, v___x_3405_);
    if v___x_3406_ == 0 {
        lean_dec(v_pos_3401_);
        lean_dec_ref(v_a_3399_);
        return v_s_3403_;
    } else {
        let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
        v___x_3407_ = lean_unsigned_to_nat(0);
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
-> *mut LeanObject {
    let mut v___x_3415_: u32 = 0;
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3415_ = 58;
    v___x_3416_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_3417_ = lean_string_push(v___x_3416_, v___x_3415_);
    return v___x_3417_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5()
-> *mut LeanObject {
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    v___x_3418_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    v___x_3421_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_3422_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = lean_box(0);
    v___x_3425_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6,
    );
    v___x_3426_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3426_, 0, v___x_3425_);
    lean_ctor_set(v___x_3426_, 1, v___x_3424_);
    return v___x_3426_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(
    mut v_a_3431_: *mut LeanObject,
    mut v_a_3432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    v___x_3433_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1;
    v_s_3434_ = l_Lake_Toml_digitPairFn(v___x_3433_, v_a_3431_, v_a_3432_);
    v_errorMsg_3435_ = lean_ctor_get(v_s_3434_, 4);
    lean_inc(v_errorMsg_3435_);
    v___x_3436_ = lean_box(0);
    v___x_3437_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3435_, v___x_3436_);
    if v___x_3437_ == 0 {
        return v_s_3434_;
    } else {
        let mut v___x_3438_: u32 = 0;
        let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_3440_: *mut LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3441_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3442_: u8 = 0;
        v___x_3438_ = 58;
        v___x_3439_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7,
        );
        v_s_3440_ = l_Lake_Toml_chFn(v___x_3438_, v___x_3439_, v_a_3431_, v_s_3434_);
        v_errorMsg_3441_ = lean_ctor_get(v_s_3440_, 4);
        lean_inc(v_errorMsg_3441_);
        v___x_3442_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3441_,
            v___x_3436_,
        );
        if v___x_3442_ == 0 {
            return v_s_3440_;
        } else {
            let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
            v___x_3443_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9;
            v___x_3444_ = l_Lake_Toml_digitPairFn(v___x_3443_, v_a_3431_, v_s_3440_);
            return v___x_3444_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(
    mut v_a_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3447_: *mut LeanObject = core::ptr::null_mut();
    v_res_3447_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_a_3445_, v_a_3446_);
    lean_dec_ref(v_a_3445_);
    return v_res_3447_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(
    mut v_allowOffset_3449_: u8,
    mut v_curr_3450_: u32,
    mut v_nextPos_3451_: *mut LeanObject,
    mut v_c_3452_: *mut LeanObject,
    mut v_s_3453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3455_: u8 = 0;
    let mut v___y_3456_: u8 = 0;
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3463_: u8 = 0;
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: u32 = 0;
    let mut v___x_3466_: u8 = 0;
    let mut v___x_3467_: u32 = 0;
    let mut v___x_3468_: u8 = 0;
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec(v_nextPos_3451_);
                    return v_s_3453_;
                } else {
                    if v_allowOffset_3449_ == 0 {
                        lean_dec(v_nextPos_3451_);
                        v___x_3457_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
                        v___x_3458_ = lean_box(0);
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
                        lean_dec(v_nextPos_3451_);
                        v___x_3469_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
                        v___x_3470_ = lean_box(0);
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
    mut v_allowOffset_3477_: *mut LeanObject,
    mut v_curr_3478_: *mut LeanObject,
    mut v_nextPos_3479_: *mut LeanObject,
    mut v_c_3480_: *mut LeanObject,
    mut v_s_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowOffset_boxed_3482_: u8 = 0;
    let mut v_curr_boxed_3483_: u32 = 0;
    let mut v_res_3484_: *mut LeanObject = core::ptr::null_mut();
    v_allowOffset_boxed_3482_ = (lean_unbox(v_allowOffset_3477_) as u8);
    v_curr_boxed_3483_ = lean_unbox_uint32(v_curr_3478_);
    lean_dec(v_curr_3478_);
    v_res_3484_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(
        v_allowOffset_boxed_3482_,
        v_curr_boxed_3483_,
        v_nextPos_3479_,
        v_c_3480_,
        v_s_3481_,
    );
    lean_dec_ref(v_c_3480_);
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
    mut v_x_3490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_512__boxed_3491_: u32 = 0;
    let mut v_res_3492_: u8 = 0;
    let mut v_r_3493_: *mut LeanObject = core::ptr::null_mut();
    v_x_512__boxed_3491_ = lean_unbox_uint32(v_x_3490_);
    lean_dec(v_x_3490_);
    v_res_3492_ =
        l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(v_x_512__boxed_3491_);
    v_r_3493_ = lean_box((v_res_3492_) as usize);
    return v_r_3493_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(
    mut v_allowOffset_3499_: u8,
    mut v_c_3500_: *mut LeanObject,
    mut v_s_3501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: u8 = 0;
    let mut v_inputString_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3506_: u32 = 0;
    let mut v___x_3507_: u32 = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3511_: u8 = 0;
    let mut v___y_3512_: u8 = 0;
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3519_: u8 = 0;
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: u32 = 0;
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: u32 = 0;
    let mut v___x_3524_: u8 = 0;
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u32 = 0;
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: u32 = 0;
    let mut v___x_3532_: u8 = 0;
    let mut v___f_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: u32 = 0;
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3546_: u8 = 0;
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3552_: u8 = 0;
    let mut v___x_3553_: u32 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: u32 = 0;
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: u32 = 0;
    let mut v___x_3561_: u8 = 0;
    let mut v___x_3562_: u32 = 0;
    let mut v___x_3563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3502_ = lean_ctor_get(v_c_3500_, 0);
                v_pos_3503_ = lean_ctor_get(v_s_3501_, 2);
                v___x_3504_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3502_, v_pos_3503_);
                if v___x_3504_ == 0 {
                    v_inputString_3505_ = lean_ctor_get(v_toInputContext_3502_, 0);
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
                        lean_inc(v_pos_3503_);
                        v___f_3533_ =
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0;
                        v_s_3534_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3501_,
                            v_c_3500_,
                            v_pos_3503_,
                        );
                        lean_dec(v_pos_3503_);
                        v___x_3535_ = lean_box(0);
                        v___x_3536_ =
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2;
                        v_s_3537_ = l_Lake_Toml_takeWhile1Fn(
                            v___f_3533_,
                            v___x_3536_,
                            v_c_3500_,
                            v_s_3534_,
                        );
                        v_pos_3538_ = lean_ctor_get(v_s_3537_, 2);
                        lean_inc(v_pos_3538_);
                        v_errorMsg_3539_ = lean_ctor_get(v_s_3537_, 4);
                        lean_inc(v_errorMsg_3539_);
                        v___x_3540_ = lean_box(0);
                        v___x_3541_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                            v_errorMsg_3539_,
                            v___x_3540_,
                        );
                        if v___x_3541_ == 0 {
                            lean_dec(v_pos_3538_);
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
                                    lean_dec(v_pos_3538_);
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
                                    lean_dec(v_pos_3538_);
                                    return v_s_3537_;
                                }
                            } else {
                                lean_dec(v_pos_3538_);
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
                        v___x_3514_ = lean_box(0);
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
                        v___x_3526_ = lean_box(0);
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
    mut v_allowOffset_3564_: *mut LeanObject,
    mut v_c_3565_: *mut LeanObject,
    mut v_s_3566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowOffset_boxed_3567_: u8 = 0;
    let mut v_res_3568_: *mut LeanObject = core::ptr::null_mut();
    v_allowOffset_boxed_3567_ = (lean_unbox(v_allowOffset_3564_) as u8);
    v_res_3568_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(
        v_allowOffset_boxed_3567_,
        v_c_3565_,
        v_s_3566_,
    );
    lean_dec_ref(v_c_3565_);
    return v_res_3568_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(
    mut v_allowOffset_3573_: u8,
    mut v_a_3574_: *mut LeanObject,
    mut v_a_3575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: u8 = 0;
    v___x_3576_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9;
    v_s_3577_ = l_Lake_Toml_digitPairFn(v___x_3576_, v_a_3574_, v_a_3575_);
    v_errorMsg_3578_ = lean_ctor_get(v_s_3577_, 4);
    lean_inc(v_errorMsg_3578_);
    v___x_3579_ = lean_box(0);
    v___x_3580_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3578_, v___x_3579_);
    if v___x_3580_ == 0 {
        return v_s_3577_;
    } else {
        let mut v___x_3581_: u32 = 0;
        let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_3583_: *mut LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3585_: u8 = 0;
        v___x_3581_ = 58;
        v___x_3582_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7,
        );
        v_s_3583_ = l_Lake_Toml_chFn(v___x_3581_, v___x_3582_, v_a_3574_, v_s_3577_);
        v_errorMsg_3584_ = lean_ctor_get(v_s_3583_, 4);
        lean_inc(v_errorMsg_3584_);
        v___x_3585_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3584_,
            v___x_3579_,
        );
        if v___x_3585_ == 0 {
            return v_s_3583_;
        } else {
            let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_3587_: *mut LeanObject = core::ptr::null_mut();
            let mut v_errorMsg_3588_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3589_: u8 = 0;
            v___x_3586_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1;
            v_s_3587_ = l_Lake_Toml_digitPairFn(v___x_3586_, v_a_3574_, v_s_3583_);
            v_errorMsg_3588_ = lean_ctor_get(v_s_3587_, 4);
            lean_inc(v_errorMsg_3588_);
            v___x_3589_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                v_errorMsg_3588_,
                v___x_3579_,
            );
            if v___x_3589_ == 0 {
                return v_s_3587_;
            } else {
                let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_allowOffset_3591_: *mut LeanObject,
    mut v_a_3592_: *mut LeanObject,
    mut v_a_3593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowOffset_boxed_3594_: u8 = 0;
    let mut v_res_3595_: *mut LeanObject = core::ptr::null_mut();
    v_allowOffset_boxed_3594_ = (lean_unbox(v_allowOffset_3591_) as u8);
    v_res_3595_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(
        v_allowOffset_boxed_3594_,
        v_a_3592_,
        v_a_3593_,
    );
    lean_dec_ref(v_a_3592_);
    return v_res_3595_;
}
pub unsafe fn l_Lake_Toml_timeFn(
    mut v_allowOffset_3600_: u8,
    mut v_a_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    v___x_3603_ = l_Lake_Toml_timeFn___closed__1;
    v_s_3604_ = l_Lake_Toml_digitPairFn(v___x_3603_, v_a_3601_, v_a_3602_);
    v_errorMsg_3605_ = lean_ctor_get(v_s_3604_, 4);
    lean_inc(v_errorMsg_3605_);
    v___x_3606_ = lean_box(0);
    v___x_3607_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3605_, v___x_3606_);
    if v___x_3607_ == 0 {
        return v_s_3604_;
    } else {
        let mut v___x_3608_: u32 = 0;
        let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_3610_: *mut LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3611_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3612_: u8 = 0;
        v___x_3608_ = 58;
        v___x_3609_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7,
        );
        v_s_3610_ = l_Lake_Toml_chFn(v___x_3608_, v___x_3609_, v_a_3601_, v_s_3604_);
        v_errorMsg_3611_ = lean_ctor_get(v_s_3610_, 4);
        lean_inc(v_errorMsg_3611_);
        v___x_3612_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3611_,
            v___x_3606_,
        );
        if v___x_3612_ == 0 {
            return v_s_3610_;
        } else {
            let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_allowOffset_3614_: *mut LeanObject,
    mut v_a_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowOffset_boxed_3617_: u8 = 0;
    let mut v_res_3618_: *mut LeanObject = core::ptr::null_mut();
    v_allowOffset_boxed_3617_ = (lean_unbox(v_allowOffset_3614_) as u8);
    v_res_3618_ = l_Lake_Toml_timeFn(v_allowOffset_boxed_3617_, v_a_3615_, v_a_3616_);
    lean_dec_ref(v_a_3615_);
    return v_res_3618_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(
    mut v_c_3619_: *mut LeanObject,
    mut v_s_3620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v_inputString_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3629_: u32 = 0;
    let mut v___x_3630_: u32 = 0;
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3632_: u32 = 0;
    let mut v___x_3633_: u8 = 0;
    let mut v___x_3634_: u32 = 0;
    let mut v___x_3635_: u8 = 0;
    let mut v_tPos_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_3621_ = lean_ctor_get(v_s_3620_, 2);
                v_toInputContext_3622_ = lean_ctor_get(v_c_3619_, 0);
                v___x_3623_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3622_, v_pos_3621_);
                if v___x_3623_ == 0 {
                    v_inputString_3624_ = lean_ctor_get(v_toInputContext_3622_, 0);
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
                                lean_inc(v_pos_3621_);
                                v_tPos_3636_ =
                                    lean_string_utf8_next_fast(v_inputString_3624_, v_pos_3621_);
                                v___x_3637_ =
                                    l_Lean_Parser_ParserState_setPos(v_s_3620_, v_tPos_3636_);
                                v_s_3638_ = l_Lake_Toml_timeFn(v___x_3625_, v_c_3619_, v___x_3637_);
                                v_errorMsg_3646_ = lean_ctor_get(v_s_3638_, 4);
                                lean_inc(v_errorMsg_3646_);
                                v___x_3647_ = lean_box(0);
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
                                        lean_dec(v_pos_3621_);
                                        return v_s_3638_;
                                    } else {
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_inc(v_pos_3621_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_inc(v_pos_3621_);
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
                lean_dec(v_pos_3621_);
                v___x_3628_ = l_Lake_Toml_timeFn(v___x_3625_, v_c_3619_, v___x_3627_);
                return v___x_3628_;
            }
            2 => {
                v_pos_3640_ = lean_ctor_get(v_s_3638_, 2);
                lean_inc(v_pos_3640_);
                v___x_3641_ = lean_nat_dec_eq(v_pos_3640_, v_tPos_3636_);
                lean_dec(v_pos_3640_);
                if v___x_3641_ == 0 {
                    lean_dec(v_pos_3621_);
                    return v_s_3638_;
                } else {
                    v___x_3642_ = l_Lean_Parser_ParserState_stackSize(v_s_3638_);
                    v___x_3643_ = lean_unsigned_to_nat(1);
                    v___x_3644_ = lean_nat_sub(v___x_3642_, v___x_3643_);
                    lean_dec(v___x_3642_);
                    v___x_3645_ =
                        l_Lean_Parser_ParserState_restore(v_s_3638_, v___x_3644_, v_pos_3621_);
                    lean_dec(v___x_3644_);
                    return v___x_3645_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(
    mut v_c_3649_: *mut LeanObject,
    mut v_s_3650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3651_: *mut LeanObject = core::ptr::null_mut();
    v_res_3651_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_c_3649_, v_s_3650_);
    lean_dec_ref(v_c_3649_);
    return v_res_3651_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2()
-> *mut LeanObject {
    let mut v___x_3656_: u32 = 0;
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    v___x_3656_ = 45;
    v___x_3657_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_3658_ = lean_string_push(v___x_3657_, v___x_3656_);
    return v___x_3658_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3()
-> *mut LeanObject {
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    v___x_3659_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    v___x_3662_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_3663_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    v___x_3665_ = lean_box(0);
    v___x_3666_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4,
    );
    v___x_3667_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    lean_ctor_set(v___x_3667_, 1, v___x_3665_);
    return v___x_3667_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(
    mut v_a_3672_: *mut LeanObject,
    mut v_a_3673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    v___x_3674_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1;
    v_s_3675_ = l_Lake_Toml_digitPairFn(v___x_3674_, v_a_3672_, v_a_3673_);
    v_errorMsg_3676_ = lean_ctor_get(v_s_3675_, 4);
    lean_inc(v_errorMsg_3676_);
    v___x_3677_ = lean_box(0);
    v___x_3678_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3676_, v___x_3677_);
    if v___x_3678_ == 0 {
        return v_s_3675_;
    } else {
        let mut v___x_3679_: u32 = 0;
        let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_3681_: *mut LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3683_: u8 = 0;
        v___x_3679_ = 45;
        v___x_3680_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5,
        );
        v_s_3681_ = l_Lake_Toml_chFn(v___x_3679_, v___x_3680_, v_a_3672_, v_s_3675_);
        v_errorMsg_3682_ = lean_ctor_get(v_s_3681_, 4);
        lean_inc(v_errorMsg_3682_);
        v___x_3683_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3682_,
            v___x_3677_,
        );
        if v___x_3683_ == 0 {
            return v_s_3681_;
        } else {
            let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_3685_: *mut LeanObject = core::ptr::null_mut();
            let mut v_errorMsg_3686_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3687_: u8 = 0;
            v___x_3684_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7;
            v_s_3685_ = l_Lake_Toml_digitPairFn(v___x_3684_, v_a_3672_, v_s_3681_);
            v_errorMsg_3686_ = lean_ctor_get(v_s_3685_, 4);
            lean_inc(v_errorMsg_3686_);
            v___x_3687_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                v_errorMsg_3686_,
                v___x_3677_,
            );
            if v___x_3687_ == 0 {
                return v_s_3685_;
            } else {
                let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
                v___x_3688_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_a_3672_, v_s_3685_);
                return v___x_3688_;
            }
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(
    mut v_a_3689_: *mut LeanObject,
    mut v_a_3690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3691_: *mut LeanObject = core::ptr::null_mut();
    v_res_3691_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_3689_, v_a_3690_);
    lean_dec_ref(v_a_3689_);
    return v_res_3691_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(
    mut v_c_3696_: *mut LeanObject,
    mut v_x_3697_: *mut LeanObject,
    mut v_x_3698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3700_: u8 = 0;
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: u8 = 0;
    let mut v_one_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3699_ = lean_unsigned_to_nat(0);
                v_isZero_3700_ = lean_nat_dec_eq(v_x_3697_, v_zero_3699_);
                if v_isZero_3700_ == 1 {
                    lean_dec(v_x_3697_);
                    return v_x_3698_;
                } else {
                    v___x_3701_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1;
                    v_s_3702_ = l_Lake_Toml_digitFn(v___x_3701_, v_c_3696_, v_x_3698_);
                    v_errorMsg_3703_ = lean_ctor_get(v_s_3702_, 4);
                    lean_inc(v_errorMsg_3703_);
                    v___x_3704_ = lean_box(0);
                    v___x_3705_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3703_,
                        v___x_3704_,
                    );
                    if v___x_3705_ == 0 {
                        lean_dec(v_x_3697_);
                        return v_s_3702_;
                    } else {
                        v_one_3706_ = lean_unsigned_to_nat(1);
                        v_n_3707_ = lean_nat_sub(v_x_3697_, v_one_3706_);
                        lean_dec(v_x_3697_);
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
    mut v_c_3709_: *mut LeanObject,
    mut v_x_3710_: *mut LeanObject,
    mut v_x_3711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3712_: *mut LeanObject = core::ptr::null_mut();
    v_res_3712_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_c_3709_, v_x_3710_, v_x_3711_);
    lean_dec_ref(v_c_3709_);
    return v_res_3712_;
}
pub unsafe fn l_Lake_Toml_dateTimeFn(
    mut v_a_3713_: *mut LeanObject,
    mut v_a_3714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: u8 = 0;
    v___x_3715_ = lean_unsigned_to_nat(4);
    v_s_3716_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_a_3713_, v___x_3715_, v_a_3714_);
    v_errorMsg_3717_ = lean_ctor_get(v_s_3716_, 4);
    lean_inc(v_errorMsg_3717_);
    v___x_3718_ = lean_box(0);
    v___x_3719_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3717_, v___x_3718_);
    if v___x_3719_ == 0 {
        return v_s_3716_;
    } else {
        let mut v___x_3720_: u32 = 0;
        let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_3722_: *mut LeanObject = core::ptr::null_mut();
        let mut v_errorMsg_3723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3724_: u8 = 0;
        v___x_3720_ = 45;
        v___x_3721_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once
            ),
            _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5,
        );
        v_s_3722_ = l_Lake_Toml_chFn(v___x_3720_, v___x_3721_, v_a_3713_, v_s_3716_);
        v_errorMsg_3723_ = lean_ctor_get(v_s_3722_, 4);
        lean_inc(v_errorMsg_3723_);
        v___x_3724_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
            v_errorMsg_3723_,
            v___x_3718_,
        );
        if v___x_3724_ == 0 {
            return v_s_3722_;
        } else {
            let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
            v___x_3725_ =
                l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_3713_, v_s_3722_);
            return v___x_3725_;
        }
    }
}
pub unsafe fn l_Lake_Toml_dateTimeFn___boxed(
    mut v_a_3726_: *mut LeanObject,
    mut v_a_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3728_: *mut LeanObject = core::ptr::null_mut();
    v_res_3728_ = l_Lake_Toml_dateTimeFn(v_a_3726_, v_a_3727_);
    lean_dec_ref(v_a_3726_);
    return v_res_3728_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(
    mut v_c_3733_: *mut LeanObject,
    mut v_s_3734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v_inputString_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: u32 = 0;
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3745_: u32 = 0;
    let mut v___x_3746_: u32 = 0;
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: u32 = 0;
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: u8 = 0;
    let mut v___y_3752_: u8 = 0;
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: u32 = 0;
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: u32 = 0;
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: u32 = 0;
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3735_ = lean_ctor_get(v_c_3733_, 0);
                v_pos_3736_ = lean_ctor_get(v_s_3734_, 2);
                v_expected_3737_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1;
                v___x_3738_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3735_, v_pos_3736_);
                if v___x_3738_ == 0 {
                    v_inputString_3739_ = lean_ctor_get(v_toInputContext_3735_, 0);
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
                            lean_inc(v_pos_3736_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_inc(v_pos_3736_);
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
                lean_dec(v_pos_3736_);
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
                    lean_inc(v_pos_3736_);
                    v_s_3754_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3734_,
                        v_c_3733_,
                        v_pos_3736_,
                    );
                    lean_dec(v_pos_3736_);
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
    mut v_c_3762_: *mut LeanObject,
    mut v_s_3763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3764_: *mut LeanObject = core::ptr::null_mut();
    v_res_3764_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_3762_, v_s_3763_);
    lean_dec_ref(v_c_3762_);
    return v_res_3764_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(
    mut v_c_3765_: *mut LeanObject,
    mut v_s_3766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: u8 = 0;
    let mut v_inputString_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3774_: u32 = 0;
    let mut v___x_3775_: u32 = 0;
    let mut v___x_3776_: u8 = 0;
    let mut v___x_3777_: u32 = 0;
    let mut v___x_3778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3767_ = lean_ctor_get(v_c_3765_, 0);
                v_pos_3768_ = lean_ctor_get(v_s_3766_, 2);
                v___x_3772_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3767_, v_pos_3768_);
                if v___x_3772_ == 0 {
                    v_inputString_3773_ = lean_ctor_get(v_toInputContext_3767_, 0);
                    v_curr_3774_ = lean_string_utf8_get_fast(v_inputString_3773_, v_pos_3768_);
                    v___x_3775_ = 101;
                    v___x_3776_ = lean_uint32_dec_eq(v_curr_3774_, v___x_3775_);
                    if v___x_3776_ == 0 {
                        v___x_3777_ = 69;
                        v___x_3778_ = lean_uint32_dec_eq(v_curr_3774_, v___x_3777_);
                        if v___x_3778_ == 0 {
                            return v_s_3766_;
                        } else {
                            lean_inc(v_pos_3768_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_inc(v_pos_3768_);
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
                lean_dec(v_pos_3768_);
                v___x_3771_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_3765_, v___x_3770_);
                return v___x_3771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(
    mut v_c_3779_: *mut LeanObject,
    mut v_s_3780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3781_: *mut LeanObject = core::ptr::null_mut();
    v_res_3781_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_3779_, v_s_3780_);
    lean_dec_ref(v_c_3779_);
    return v_res_3781_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(
    mut v_startPos_3799_: *mut LeanObject,
    mut v_curr_3800_: u32,
    mut v_nextPos_3801_: *mut LeanObject,
    mut v_c_3802_: *mut LeanObject,
    mut v_s_3803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: u32 = 0;
    let mut v___x_3810_: u8 = 0;
    let mut v_s_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: u32 = 0;
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: u32 = 0;
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u32 = 0;
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: u8 = 0;
    let mut v_errorMsg_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
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
                            lean_dec(v_nextPos_3801_);
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
                    v_errorMsg_3837_ = lean_ctor_get(v_s_3831_, 4);
                    lean_inc(v_errorMsg_3837_);
                    v___x_3838_ = lean_box(0);
                    v___x_3839_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                        v_errorMsg_3837_,
                        v___x_3838_,
                    );
                    if v___x_3839_ == 0 {
                        if v___x_3810_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            lean_dec_ref(v_c_3802_);
                            lean_dec(v_startPos_3799_);
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
                v_errorMsg_3814_ = lean_ctor_get(v_s_3813_, 4);
                lean_inc(v_errorMsg_3814_);
                v___x_3815_ = lean_box(0);
                v___x_3816_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                    v_errorMsg_3814_,
                    v___x_3815_,
                );
                if v___x_3816_ == 0 {
                    lean_dec_ref(v_c_3802_);
                    lean_dec(v_startPos_3799_);
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
                        lean_dec_ref(v_c_3802_);
                        lean_dec(v_startPos_3799_);
                        return v_s_3813_;
                    }
                }
            }
            3 => {
                v_s_3833_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_3802_, v_s_3831_);
                v_errorMsg_3834_ = lean_ctor_get(v_s_3833_, 4);
                lean_inc(v_errorMsg_3834_);
                v___x_3835_ = lean_box(0);
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
                        lean_dec_ref(v_c_3802_);
                        lean_dec(v_startPos_3799_);
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
    mut v_startPos_3840_: *mut LeanObject,
    mut v_curr_3841_: *mut LeanObject,
    mut v_nextPos_3842_: *mut LeanObject,
    mut v_c_3843_: *mut LeanObject,
    mut v_s_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_curr_boxed_3845_: u32 = 0;
    let mut v_res_3846_: *mut LeanObject = core::ptr::null_mut();
    v_curr_boxed_3845_ = lean_unbox_uint32(v_curr_3841_);
    lean_dec(v_curr_3841_);
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
    mut v_startPos_3847_: *mut LeanObject,
    mut v_c_3848_: *mut LeanObject,
    mut v_s_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: u8 = 0;
    v_toInputContext_3850_ = lean_ctor_get(v_c_3848_, 0);
    v_pos_3851_ = lean_ctor_get(v_s_3849_, 2);
    v___x_3852_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3850_, v_pos_3851_);
    if v___x_3852_ == 0 {
        let mut v_inputString_3853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3854_: u32 = 0;
        let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
        v_inputString_3853_ = lean_ctor_get(v_toInputContext_3850_, 0);
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
        let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_startPos_3867_: *mut LeanObject,
    mut v_c_3868_: *mut LeanObject,
    mut v_s_3869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u8 = 0;
    let mut v_inputString_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3874_: u32 = 0;
    let mut v___y_3876_: u8 = 0;
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u32 = 0;
    let mut v___x_3882_: u8 = 0;
    let mut v___x_3883_: u32 = 0;
    let mut v___x_3884_: u8 = 0;
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3870_ = lean_ctor_get(v_c_3868_, 0);
                v_pos_3871_ = lean_ctor_get(v_s_3869_, 2);
                v___x_3872_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3870_, v_pos_3871_);
                if v___x_3872_ == 0 {
                    v_inputString_3873_ = lean_ctor_get(v_toInputContext_3870_, 0);
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
                    lean_inc(v_pos_3871_);
                    v_s_3879_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3869_,
                        v_c_3868_,
                        v_pos_3871_,
                    );
                    lean_dec(v_pos_3871_);
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
    mut v_startPos_3888_: *mut LeanObject,
    mut v_c_3889_: *mut LeanObject,
    mut v_s_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: u8 = 0;
    let mut v_inputString_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: u8 = 0;
    let mut v_curr_3897_: u32 = 0;
    let mut v___y_3899_: u8 = 0;
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: u32 = 0;
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: u32 = 0;
    let mut v___x_3906_: u8 = 0;
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_3891_ = lean_ctor_get(v_s_3890_, 2);
                v_toInputContext_3892_ = lean_ctor_get(v_c_3889_, 0);
                v_expected_3893_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2;
                v___x_3894_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3892_, v_pos_3891_);
                if v___x_3894_ == 0 {
                    v_inputString_3895_ = lean_ctor_get(v_toInputContext_3892_, 0);
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
                    lean_dec_ref(v_c_3889_);
                    lean_dec(v_startPos_3888_);
                    v___x_3907_ = l_Lean_Parser_ParserState_mkEOIError(v_s_3890_, v_expected_3893_);
                    return v___x_3907_;
                }
            }
            1 => {
                if v___y_3899_ == 0 {
                    lean_dec_ref(v_c_3889_);
                    lean_dec(v_startPos_3888_);
                    v___x_3900_ = l_Lake_Toml_mkUnexpectedCharError(
                        v_s_3890_,
                        v_curr_3897_,
                        v_expected_3893_,
                        v___x_3896_,
                    );
                    return v___x_3900_;
                } else {
                    lean_inc(v_pos_3891_);
                    v_s_3901_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3890_,
                        v_c_3889_,
                        v_pos_3891_,
                    );
                    lean_dec(v_pos_3891_);
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
    mut v_startPos_3908_: *mut LeanObject,
    mut v_curr_3909_: u32,
    mut v_nextPos_3910_: *mut LeanObject,
    mut v_c_3911_: *mut LeanObject,
    mut v_s_3912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3913_: u32 = 0;
    let mut v___x_3914_: u8 = 0;
    v___x_3913_ = 95;
    v___x_3914_ = lean_uint32_dec_eq(v_curr_3909_, v___x_3913_);
    if v___x_3914_ == 0 {
        let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
        v___x_3915_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(
            v_startPos_3908_,
            v_curr_3909_,
            v_nextPos_3910_,
            v_c_3911_,
            v_s_3912_,
        );
        return v___x_3915_;
    } else {
        let mut v_s_3916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_startPos_3918_: *mut LeanObject,
    mut v_curr_3919_: *mut LeanObject,
    mut v_nextPos_3920_: *mut LeanObject,
    mut v_c_3921_: *mut LeanObject,
    mut v_s_3922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_curr_boxed_3923_: u32 = 0;
    let mut v_res_3924_: *mut LeanObject = core::ptr::null_mut();
    v_curr_boxed_3923_ = lean_unbox_uint32(v_curr_3919_);
    lean_dec(v_curr_3919_);
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
    mut v_startPos_3930_: *mut LeanObject,
    mut v_a_3931_: *mut LeanObject,
    mut v_a_3932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: u8 = 0;
    v___x_3933_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0;
    v___x_3934_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2;
    lean_inc_ref(v_a_3931_);
    v_s_3935_ = l_Lake_Toml_strFn(v___x_3933_, v___x_3934_, v_a_3931_, v_a_3932_);
    v_errorMsg_3936_ = lean_ctor_get(v_s_3935_, 4);
    lean_inc(v_errorMsg_3936_);
    v___x_3937_ = lean_box(0);
    v___x_3938_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3936_, v___x_3937_);
    if v___x_3938_ == 0 {
        lean_dec_ref(v_a_3931_);
        lean_dec(v_startPos_3930_);
        return v_s_3935_;
    } else {
        let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_startPos_3947_: *mut LeanObject,
    mut v_a_3948_: *mut LeanObject,
    mut v_a_3949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: u8 = 0;
    v___x_3950_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0;
    v___x_3951_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2;
    lean_inc_ref(v_a_3948_);
    v_s_3952_ = l_Lake_Toml_strFn(v___x_3950_, v___x_3951_, v_a_3948_, v_a_3949_);
    v_errorMsg_3953_ = lean_ctor_get(v_s_3952_, 4);
    lean_inc(v_errorMsg_3953_);
    v___x_3954_ = lean_box(0);
    v___x_3955_ =
        l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_3953_, v___x_3954_);
    if v___x_3955_ == 0 {
        lean_dec_ref(v_a_3948_);
        lean_dec(v_startPos_3947_);
        return v_s_3952_;
    } else {
        let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_startPos_3959_: *mut LeanObject,
    mut v_c_3960_: *mut LeanObject,
    mut v_s_3961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toInputContext_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v_inputString_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_3967_: u32 = 0;
    let mut v___x_3968_: u32 = 0;
    let mut v___x_3969_: u8 = 0;
    let mut v___x_3970_: u8 = 0;
    let mut v___y_3972_: u8 = 0;
    let mut v___x_3973_: u32 = 0;
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3975_: u32 = 0;
    let mut v___x_3976_: u8 = 0;
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: u32 = 0;
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_3962_ = lean_ctor_get(v_c_3960_, 0);
                v_pos_3963_ = lean_ctor_get(v_s_3961_, 2);
                v_expected_3964_ =
                    l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2;
                v___x_3965_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3962_, v_pos_3963_);
                if v___x_3965_ == 0 {
                    v_inputString_3966_ = lean_ctor_get(v_toInputContext_3962_, 0);
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
                        lean_inc(v_pos_3963_);
                        v___x_3987_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3961_,
                            v_c_3960_,
                            v_pos_3963_,
                        );
                        lean_dec(v_pos_3963_);
                        v___x_3988_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(
                            v_startPos_3959_,
                            v_c_3960_,
                            v___x_3987_,
                        );
                        return v___x_3988_;
                    }
                } else {
                    lean_dec_ref(v_c_3960_);
                    lean_dec(v_startPos_3959_);
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
                            lean_dec_ref(v_c_3960_);
                            lean_dec(v_startPos_3959_);
                            v___x_3977_ = l_Lake_Toml_mkUnexpectedCharError(
                                v_s_3961_,
                                v_curr_3967_,
                                v_expected_3964_,
                                v___x_3970_,
                            );
                            return v___x_3977_;
                        } else {
                            lean_inc(v_pos_3963_);
                            v___x_3978_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_3961_,
                                v_c_3960_,
                                v_pos_3963_,
                            );
                            lean_dec(v_pos_3963_);
                            v___x_3979_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(
                                v_startPos_3959_,
                                v_c_3960_,
                                v___x_3978_,
                            );
                            return v___x_3979_;
                        }
                    } else {
                        lean_inc(v_pos_3963_);
                        v___x_3980_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_3961_,
                            v_c_3960_,
                            v_pos_3963_,
                        );
                        lean_dec(v_pos_3963_);
                        v___x_3981_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(
                            v_startPos_3959_,
                            v_c_3960_,
                            v___x_3980_,
                        );
                        return v___x_3981_;
                    }
                } else {
                    lean_inc(v_pos_3963_);
                    v___x_3982_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_s_3961_,
                        v_c_3960_,
                        v_pos_3963_,
                    );
                    lean_dec(v_pos_3963_);
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
    mut v_startPos_4005_: *mut LeanObject,
    mut v_c_4006_: *mut LeanObject,
    mut v_s_4007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4011_: u32 = 0;
    let mut v___y_4012_: u8 = 0;
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4018_: u8 = 0;
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4024_: u8 = 0;
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v_inputString_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: u32 = 0;
    let mut v___y_4036_: u8 = 0;
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v_pos_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_4041_: u32 = 0;
    let mut v_nextPos_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: u32 = 0;
    let mut v___x_4044_: u8 = 0;
    let mut v___x_4045_: u32 = 0;
    let mut v___x_4046_: u8 = 0;
    let mut v___x_4047_: u32 = 0;
    let mut v___x_4048_: u8 = 0;
    let mut v_s_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: u32 = 0;
    let mut v___y_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4061_: u8 = 0;
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    let mut v_curr_4066_: u32 = 0;
    let mut v_nextPos_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: u32 = 0;
    let mut v___x_4069_: u8 = 0;
    let mut v___x_4070_: u32 = 0;
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_curr_4075_: u32 = 0;
    let mut v_nextPos_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4078_: u8 = 0;
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: u8 = 0;
    let mut v_curr_4083_: u32 = 0;
    let mut v_nextPos_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u32 = 0;
    let mut v___x_4086_: u8 = 0;
    let mut v___x_4087_: u32 = 0;
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: u32 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v_s_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u32 = 0;
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: u32 = 0;
    let mut v___x_4102_: u8 = 0;
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_4028_ = lean_ctor_get(v_c_4006_, 0);
                v_pos_4029_ = lean_ctor_get(v_s_4007_, 2);
                v___x_4030_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4028_, v_pos_4029_);
                if v___x_4030_ == 0 {
                    v_inputString_4031_ = lean_ctor_get(v_toInputContext_4028_, 0);
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
                    lean_dec_ref(v_c_4006_);
                    lean_dec(v_startPos_4005_);
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
                    lean_dec_ref(v_c_4006_);
                    lean_dec(v_startPos_4005_);
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
                    lean_dec_ref(v_c_4006_);
                    lean_dec(v_startPos_4005_);
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
                    lean_inc(v___y_4033_);
                    v_s_4038_ = l_Lean_Parser_ParserState_setPos(v___y_4034_, v___y_4033_);
                    v___x_4039_ =
                        l_Lean_Parser_InputContext_atEnd(v_toInputContext_4028_, v___y_4033_);
                    lean_dec(v___y_4033_);
                    if v___x_4039_ == 0 {
                        v_pos_4040_ = lean_ctor_get(v_s_4038_, 2);
                        lean_inc(v_pos_4040_);
                        v_curr_4041_ = lean_string_utf8_get_fast(v_inputString_4031_, v_pos_4040_);
                        v_nextPos_4042_ =
                            lean_string_utf8_next_fast(v_inputString_4031_, v_pos_4040_);
                        lean_dec(v_pos_4040_);
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
                            v_errorMsg_4051_ = lean_ctor_get(v_s_4050_, 4);
                            lean_inc(v_errorMsg_4051_);
                            v___x_4052_ = lean_box(0);
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
                    v_pos_4064_ = lean_ctor_get(v_s_4063_, 2);
                    lean_inc(v_pos_4064_);
                    v___x_4065_ =
                        l_Lean_Parser_InputContext_atEnd(v_toInputContext_4028_, v_pos_4064_);
                    if v___x_4065_ == 0 {
                        v_curr_4066_ = lean_string_utf8_get_fast(v_inputString_4031_, v_pos_4064_);
                        v_nextPos_4067_ =
                            lean_string_utf8_next_fast(v_inputString_4031_, v_pos_4064_);
                        lean_dec(v_pos_4064_);
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
                        lean_dec(v_pos_4064_);
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
                    v_pos_4081_ = lean_ctor_get(v_s_4080_, 2);
                    lean_inc(v_pos_4081_);
                    v___x_4082_ =
                        l_Lean_Parser_InputContext_atEnd(v_toInputContext_4028_, v_pos_4081_);
                    if v___x_4082_ == 0 {
                        v_curr_4083_ = lean_string_utf8_get_fast(v_inputString_4031_, v_pos_4081_);
                        v_nextPos_4084_ =
                            lean_string_utf8_next_fast(v_inputString_4031_, v_pos_4081_);
                        lean_dec(v_pos_4081_);
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
                            v_errorMsg_4093_ = lean_ctor_get(v_s_4092_, 4);
                            lean_inc(v_errorMsg_4093_);
                            v___x_4094_ = lean_box(0);
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
                        lean_dec(v_pos_4081_);
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
    mut v_c_4140_: *mut LeanObject,
    mut v_s_4141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: u8 = 0;
    let mut v_inputString_4149_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4178_: u32 = 0;
    let mut v___x_4179_: u8 = 0;
    let mut v_s_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: u8 = 0;
    let mut v_curr_4183_: u32 = 0;
    let mut v___x_4184_: u32 = 0;
    let mut v___x_4185_: u8 = 0;
    let mut v___x_4186_: u32 = 0;
    let mut v___x_4187_: u8 = 0;
    let mut v___x_4188_: u32 = 0;
    let mut v___x_4189_: u8 = 0;
    let mut v___y_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: u8 = 0;
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4199_: u8 = 0;
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u32 = 0;
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: u8 = 0;
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: u8 = 0;
    let mut v___x_4211_: u32 = 0;
    let mut v___x_4212_: u8 = 0;
    let mut v_s_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: u32 = 0;
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4219_: u8 = 0;
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: u8 = 0;
    let mut v_s_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u32 = 0;
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4232_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: u8 = 0;
    let mut v_s_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: u32 = 0;
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4245_: u8 = 0;
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_4142_ = lean_ctor_get(v_s_4141_, 2);
                v_toInputContext_4146_ = lean_ctor_get(v_c_4140_, 0);
                v_expected_4147_ = l_Lake_Toml_numeralFn___lam__0___closed__1;
                v___x_4148_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4146_, v_pos_4142_);
                if v___x_4148_ == 0 {
                    v_inputString_4149_ = lean_ctor_get(v_toInputContext_4146_, 0);
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
                        lean_inc(v_pos_4142_);
                        v_s_4180_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_4141_,
                            v_c_4140_,
                            v_pos_4142_,
                        );
                        v_pos_4181_ = lean_ctor_get(v_s_4180_, 2);
                        lean_inc(v_pos_4181_);
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
                                        lean_dec(v_pos_4181_);
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
                                        v_errorMsg_4223_ = lean_ctor_get(v_s_4217_, 4);
                                        lean_inc(v_errorMsg_4223_);
                                        v___x_4224_ = lean_box(0);
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
                                    lean_dec(v_pos_4181_);
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
                                    v_errorMsg_4236_ = lean_ctor_get(v_s_4230_, 4);
                                    lean_inc(v_errorMsg_4236_);
                                    v___x_4237_ = lean_box(0);
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
                                lean_dec(v_pos_4181_);
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
                                v_errorMsg_4249_ = lean_ctor_get(v_s_4243_, 4);
                                lean_inc(v_errorMsg_4249_);
                                v___x_4250_ = lean_box(0);
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
                            lean_dec(v_pos_4181_);
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
                    lean_dec_ref(v_c_4140_);
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
                                    lean_dec_ref(v_c_4140_);
                                    v___x_4164_ = l_Lake_Toml_numeralFn___lam__0___closed__2;
                                    v___x_4165_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
                                    v___x_4166_ = lean_string_push(v___x_4165_, v_curr_4150_);
                                    v___x_4167_ = lean_string_append(v___x_4164_, v___x_4166_);
                                    lean_dec_ref(v___x_4166_);
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
                                    lean_inc(v_pos_4142_);
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
                                lean_inc(v_pos_4142_);
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
                            lean_inc(v_pos_4142_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_inc(v_pos_4142_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc(v_pos_4142_);
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
                v_errorMsg_4192_ = lean_ctor_get(v___y_4191_, 4);
                v___x_4193_ = lean_box(0);
                lean_inc(v_errorMsg_4192_);
                v___x_4194_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(
                    v_errorMsg_4192_,
                    v___x_4193_,
                );
                if v___x_4194_ == 0 {
                    lean_dec(v_pos_4142_);
                    lean_dec_ref(v_c_4140_);
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
                        lean_dec(v_pos_4142_);
                        lean_dec_ref(v_c_4140_);
                        return v___y_4191_;
                    }
                }
            }
            4 => {
                if v___y_4199_ == 0 {
                    v___x_4200_ = lean_string_utf8_next_fast(v_inputString_4149_, v_pos_4181_);
                    lean_dec(v_pos_4181_);
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
                    lean_dec(v_pos_4181_);
                    v___x_4203_ = 58;
                    v___x_4204_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once
                        ),
                        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7,
                    );
                    v_s_4205_ = l_Lake_Toml_chFn(v___x_4203_, v___x_4204_, v_c_4140_, v_s_4202_);
                    v_errorMsg_4206_ = lean_ctor_get(v_s_4205_, 4);
                    lean_inc(v_errorMsg_4206_);
                    v___x_4207_ = lean_box(0);
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
                    lean_dec(v_pos_4142_);
                    lean_dec_ref(v_c_4140_);
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
                    lean_dec(v_pos_4142_);
                    lean_dec_ref(v_c_4140_);
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
                    lean_dec(v_pos_4142_);
                    lean_dec_ref(v_c_4140_);
                    return v_s_4243_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_numeralFn(
    mut v_a_4257_: *mut LeanObject,
    mut v_a_4258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    v___f_4259_ = l_Lake_Toml_numeralFn___closed__0;
    v___x_4260_ = l_Lean_Parser_atomicFn(v___f_4259_, v_a_4257_, v_a_4258_);
    return v___x_4260_;
}
pub unsafe fn _init_l_Lake_Toml_trailingWs___closed__0() -> *mut LeanObject {
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    v___x_4261_ = lean_alloc_closure(l_Lake_Toml_wsFn___boxed as *mut core::ffi::c_void, 2, 0);
    v___x_4262_ = l_Lake_Toml_trailing(v___x_4261_);
    return v___x_4262_;
}
pub unsafe fn _init_l_Lake_Toml_trailingWs() -> *mut LeanObject {
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    v___x_4263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_trailingWs___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_trailingWs___closed__0_once),
        _init_l_Lake_Toml_trailingWs___closed__0,
    );
    return v___x_4263_;
}
pub unsafe fn _init_l_Lake_Toml_trailingSep___closed__1() -> *mut LeanObject {
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    v___x_4265_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4266_ = l_Lake_Toml_trailing(v___x_4265_);
    return v___x_4266_;
}
pub unsafe fn _init_l_Lake_Toml_trailingSep() -> *mut LeanObject {
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    v___x_4267_ = lean_obj_once(
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
    mut v_c_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_4291_: u32 = 0;
    let mut v_res_4292_: u8 = 0;
    let mut v_r_4293_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_4291_ = lean_unbox_uint32(v_c_4290_);
    lean_dec(v_c_4290_);
    v_res_4292_ = l_Lake_Toml_unquotedKeyFn___lam__0(v_c_boxed_4291_);
    v_r_4293_ = lean_box((v_res_4292_) as usize);
    return v_r_4293_;
}
pub unsafe fn l_Lake_Toml_unquotedKeyFn(
    mut v_a_4299_: *mut LeanObject,
    mut v_a_4300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    v___f_4301_ = l_Lake_Toml_unquotedKeyFn___closed__0;
    v___x_4302_ = l_Lake_Toml_unquotedKeyFn___closed__2;
    v___x_4303_ = l_Lake_Toml_takeWhile1Fn(v___f_4301_, v___x_4302_, v_a_4299_, v_a_4300_);
    return v___x_4303_;
}
pub unsafe fn l_Lake_Toml_unquotedKeyFn___boxed(
    mut v_a_4304_: *mut LeanObject,
    mut v_a_4305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4306_: *mut LeanObject = core::ptr::null_mut();
    v_res_4306_ = l_Lake_Toml_unquotedKeyFn(v_a_4304_, v_a_4305_);
    lean_dec_ref(v_a_4304_);
    return v_res_4306_;
}
pub unsafe fn _init_l_Lake_Toml_unquotedKey___closed__2() -> *mut LeanObject {
    let mut v___x_4312_: u8 = 0;
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    v___x_4312_ = 0;
    v___x_4313_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4314_ = lean_alloc_closure(
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
pub unsafe fn _init_l_Lake_Toml_unquotedKey() -> *mut LeanObject {
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    v___x_4318_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_unquotedKey___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_unquotedKey___closed__2_once),
        _init_l_Lake_Toml_unquotedKey___closed__2,
    );
    return v___x_4318_;
}
pub unsafe fn _init_l_Lake_Toml_basicString___closed__2() -> *mut LeanObject {
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    v___x_4324_ = 0;
    v___x_4325_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4326_ = lean_alloc_closure(l_Lake_Toml_basicStringFn as *mut core::ffi::c_void, 2, 0);
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
pub unsafe fn _init_l_Lake_Toml_basicString() -> *mut LeanObject {
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    v___x_4330_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_basicString___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_basicString___closed__2_once),
        _init_l_Lake_Toml_basicString___closed__2,
    );
    return v___x_4330_;
}
pub unsafe fn _init_l_Lake_Toml_literalString___closed__2() -> *mut LeanObject {
    let mut v___x_4336_: u8 = 0;
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    v___x_4336_ = 0;
    v___x_4337_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4338_ = lean_alloc_closure(
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
pub unsafe fn _init_l_Lake_Toml_literalString() -> *mut LeanObject {
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    v___x_4342_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_literalString___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_literalString___closed__2_once),
        _init_l_Lake_Toml_literalString___closed__2,
    );
    return v___x_4342_;
}
pub unsafe fn _init_l_Lake_Toml_mlBasicString___closed__2() -> *mut LeanObject {
    let mut v___x_4348_: u8 = 0;
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    v___x_4348_ = 0;
    v___x_4349_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4350_ = lean_alloc_closure(l_Lake_Toml_mlBasicStringFn as *mut core::ffi::c_void, 2, 0);
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
pub unsafe fn _init_l_Lake_Toml_mlBasicString() -> *mut LeanObject {
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    v___x_4354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_mlBasicString___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_mlBasicString___closed__2_once),
        _init_l_Lake_Toml_mlBasicString___closed__2,
    );
    return v___x_4354_;
}
pub unsafe fn _init_l_Lake_Toml_mlLiteralString___closed__2() -> *mut LeanObject {
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    v___x_4360_ = 0;
    v___x_4361_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4362_ = lean_alloc_closure(
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
pub unsafe fn _init_l_Lake_Toml_mlLiteralString() -> *mut LeanObject {
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    v___x_4366_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_mlLiteralString___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_mlLiteralString___closed__2_once),
        _init_l_Lake_Toml_mlLiteralString___closed__2,
    );
    return v___x_4366_;
}
pub unsafe fn _init_l_Lake_Toml_quotedKey___closed__0() -> *mut LeanObject {
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    v___x_4367_ = l_Lake_Toml_literalString;
    v___x_4368_ = l_Lake_Toml_basicString;
    v___x_4369_ = l_Lean_Parser_orelse(v___x_4368_, v___x_4367_);
    return v___x_4369_;
}
pub unsafe fn _init_l_Lake_Toml_quotedKey() -> *mut LeanObject {
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    v___x_4370_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_quotedKey___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_quotedKey___closed__0_once),
        _init_l_Lake_Toml_quotedKey___closed__0,
    );
    return v___x_4370_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey___closed__2() -> *mut LeanObject {
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    v___x_4376_ = l_Lake_Toml_quotedKey;
    v___x_4377_ = l_Lake_Toml_unquotedKey;
    v___x_4378_ = l_Lean_Parser_orelse(v___x_4377_, v___x_4376_);
    return v___x_4378_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey___closed__3() -> *mut LeanObject {
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    v___x_4379_ = 1;
    v___x_4380_ = lean_obj_once(
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
pub unsafe fn _init_l_Lake_Toml_simpleKey() -> *mut LeanObject {
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    v___x_4384_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_simpleKey___closed__3_once),
        _init_l_Lake_Toml_simpleKey___closed__3,
    );
    return v___x_4384_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__4() -> *mut LeanObject {
    let mut v___x_4394_: u32 = 0;
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    v___x_4394_ = 46;
    v___x_4395_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4396_ = lean_string_push(v___x_4395_, v___x_4394_);
    return v___x_4396_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__5() -> *mut LeanObject {
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    v___x_4397_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__4_once),
        _init_l_Lake_Toml_key___closed__4,
    );
    v___x_4398_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4399_ = lean_string_append(v___x_4398_, v___x_4397_);
    return v___x_4399_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__6() -> *mut LeanObject {
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    v___x_4400_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4401_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__5_once),
        _init_l_Lake_Toml_key___closed__5,
    );
    v___x_4402_ = lean_string_append(v___x_4401_, v___x_4400_);
    return v___x_4402_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__7() -> *mut LeanObject {
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    v___x_4403_ = lean_box(0);
    v___x_4404_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__6_once),
        _init_l_Lake_Toml_key___closed__6,
    );
    v___x_4405_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4405_, 0, v___x_4404_);
    lean_ctor_set(v___x_4405_, 1, v___x_4403_);
    return v___x_4405_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__8() -> *mut LeanObject {
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u32 = 0;
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    v___x_4406_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4407_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7_once),
        _init_l_Lake_Toml_key___closed__7,
    );
    v___x_4408_ = 46;
    v___x_4409_ = l_Lake_Toml_chAtom(v___x_4408_, v___x_4407_, v___x_4406_);
    return v___x_4409_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__9() -> *mut LeanObject {
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    v___x_4410_ = l_Lake_Toml_trailingWs;
    v___x_4411_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__8_once),
        _init_l_Lake_Toml_key___closed__8,
    );
    v___x_4412_ = l_Lean_Parser_andthen(v___x_4411_, v___x_4410_);
    return v___x_4412_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__10() -> *mut LeanObject {
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    v___x_4413_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__9_once),
        _init_l_Lake_Toml_key___closed__9,
    );
    v___x_4414_ = l_Lake_Toml_trailingWs;
    v___x_4415_ = l_Lean_Parser_andthen(v___x_4414_, v___x_4413_);
    return v___x_4415_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__11() -> *mut LeanObject {
    let mut v___x_4416_: u8 = 0;
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    v___x_4416_ = 0;
    v___x_4417_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__10),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__10_once),
        _init_l_Lake_Toml_key___closed__10,
    );
    v___x_4418_ = l_Lake_Toml_key___closed__3;
    v___x_4419_ = l_Lake_Toml_simpleKey;
    v___x_4420_ = l_Lean_Parser_sepBy1(v___x_4419_, v___x_4418_, v___x_4417_, v___x_4416_);
    return v___x_4420_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__12() -> *mut LeanObject {
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    v___x_4421_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__11),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__11_once),
        _init_l_Lake_Toml_key___closed__11,
    );
    v___x_4422_ = l_Lake_Toml_key___closed__2;
    v___x_4423_ = l_Lean_Parser_setExpected(v___x_4422_, v___x_4421_);
    return v___x_4423_;
}
pub unsafe fn _init_l_Lake_Toml_key___closed__13() -> *mut LeanObject {
    let mut v___x_4424_: u8 = 0;
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    v___x_4424_ = 1;
    v___x_4425_ = lean_obj_once(
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
pub unsafe fn _init_l_Lake_Toml_key() -> *mut LeanObject {
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    v___x_4429_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__13),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__13_once),
        _init_l_Lake_Toml_key___closed__13,
    );
    return v___x_4429_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__4() -> *mut LeanObject {
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: u32 = 0;
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    v___x_4439_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4440_ = l_Lake_Toml_stdTable___closed__3;
    v___x_4441_ = 91;
    v___x_4442_ = l_Lake_Toml_chAtom(v___x_4441_, v___x_4440_, v___x_4439_);
    return v___x_4442_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__5() -> *mut LeanObject {
    let mut v___x_4443_: u32 = 0;
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    v___x_4443_ = 91;
    v___x_4444_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4445_ = lean_string_push(v___x_4444_, v___x_4443_);
    return v___x_4445_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__6() -> *mut LeanObject {
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    v___x_4446_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__5_once),
        _init_l_Lake_Toml_stdTable___closed__5,
    );
    v___x_4447_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4448_ = lean_string_append(v___x_4447_, v___x_4446_);
    return v___x_4448_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__7() -> *mut LeanObject {
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    v___x_4449_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4450_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__6_once),
        _init_l_Lake_Toml_stdTable___closed__6,
    );
    v___x_4451_ = lean_string_append(v___x_4450_, v___x_4449_);
    return v___x_4451_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__8() -> *mut LeanObject {
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    v___x_4452_ = lean_box(0);
    v___x_4453_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__7_once),
        _init_l_Lake_Toml_stdTable___closed__7,
    );
    v___x_4454_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4454_, 0, v___x_4453_);
    lean_ctor_set(v___x_4454_, 1, v___x_4452_);
    return v___x_4454_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__9() -> *mut LeanObject {
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: u32 = 0;
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    v___x_4455_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4456_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8_once),
        _init_l_Lake_Toml_stdTable___closed__8,
    );
    v___x_4457_ = 91;
    v___x_4458_ = l_Lake_Toml_chAtom(v___x_4457_, v___x_4456_, v___x_4455_);
    return v___x_4458_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__11() -> *mut LeanObject {
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lake_Toml_stdTable___closed__10;
    v___x_4461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__9_once),
        _init_l_Lake_Toml_stdTable___closed__9,
    );
    v___x_4462_ = l_Lean_Parser_notFollowedBy(v___x_4461_, v___x_4460_);
    return v___x_4462_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__12() -> *mut LeanObject {
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    v___x_4463_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__11),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__11_once),
        _init_l_Lake_Toml_stdTable___closed__11,
    );
    v___x_4464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__4_once),
        _init_l_Lake_Toml_stdTable___closed__4,
    );
    v___x_4465_ = l_Lean_Parser_andthen(v___x_4464_, v___x_4463_);
    return v___x_4465_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__13() -> *mut LeanObject {
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    v___x_4466_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__12),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__12_once),
        _init_l_Lake_Toml_stdTable___closed__12,
    );
    v___x_4467_ = l_Lean_Parser_atomic(v___x_4466_);
    return v___x_4467_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__14() -> *mut LeanObject {
    let mut v___x_4468_: u32 = 0;
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    v___x_4468_ = 93;
    v___x_4469_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4470_ = lean_string_push(v___x_4469_, v___x_4468_);
    return v___x_4470_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__15() -> *mut LeanObject {
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    v___x_4471_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__14),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__14_once),
        _init_l_Lake_Toml_stdTable___closed__14,
    );
    v___x_4472_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4473_ = lean_string_append(v___x_4472_, v___x_4471_);
    return v___x_4473_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__16() -> *mut LeanObject {
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    v___x_4474_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4475_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__15),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__15_once),
        _init_l_Lake_Toml_stdTable___closed__15,
    );
    v___x_4476_ = lean_string_append(v___x_4475_, v___x_4474_);
    return v___x_4476_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__17() -> *mut LeanObject {
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    v___x_4477_ = lean_box(0);
    v___x_4478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__16),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__16_once),
        _init_l_Lake_Toml_stdTable___closed__16,
    );
    v___x_4479_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4479_, 0, v___x_4478_);
    lean_ctor_set(v___x_4479_, 1, v___x_4477_);
    return v___x_4479_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__18() -> *mut LeanObject {
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: u32 = 0;
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    v___x_4480_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4481_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17_once),
        _init_l_Lake_Toml_stdTable___closed__17,
    );
    v___x_4482_ = 93;
    v___x_4483_ = l_Lake_Toml_chAtom(v___x_4482_, v___x_4481_, v___x_4480_);
    return v___x_4483_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__19() -> *mut LeanObject {
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    v___x_4484_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18_once),
        _init_l_Lake_Toml_stdTable___closed__18,
    );
    v___x_4485_ = l_Lake_Toml_trailingWs;
    v___x_4486_ = l_Lean_Parser_andthen(v___x_4485_, v___x_4484_);
    return v___x_4486_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__20() -> *mut LeanObject {
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    v___x_4487_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__19),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__19_once),
        _init_l_Lake_Toml_stdTable___closed__19,
    );
    v___x_4488_ = l_Lake_Toml_key;
    v___x_4489_ = l_Lean_Parser_andthen(v___x_4488_, v___x_4487_);
    return v___x_4489_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__21() -> *mut LeanObject {
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    v___x_4490_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__20),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__20_once),
        _init_l_Lake_Toml_stdTable___closed__20,
    );
    v___x_4491_ = l_Lake_Toml_trailingWs;
    v___x_4492_ = l_Lean_Parser_andthen(v___x_4491_, v___x_4490_);
    return v___x_4492_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__22() -> *mut LeanObject {
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    v___x_4493_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__21),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__21_once),
        _init_l_Lake_Toml_stdTable___closed__21,
    );
    v___x_4494_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__13),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__13_once),
        _init_l_Lake_Toml_stdTable___closed__13,
    );
    v___x_4495_ = l_Lean_Parser_andthen(v___x_4494_, v___x_4493_);
    return v___x_4495_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable___closed__23() -> *mut LeanObject {
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    v___x_4496_ = 0;
    v___x_4497_ = lean_obj_once(
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
pub unsafe fn _init_l_Lake_Toml_stdTable() -> *mut LeanObject {
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    v___x_4501_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__23),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__23_once),
        _init_l_Lake_Toml_stdTable___closed__23,
    );
    return v___x_4501_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__2() -> *mut LeanObject {
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    v___x_4507_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__9_once),
        _init_l_Lake_Toml_stdTable___closed__9,
    );
    v___x_4508_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__4_once),
        _init_l_Lake_Toml_stdTable___closed__4,
    );
    v___x_4509_ = l_Lean_Parser_andthen(v___x_4508_, v___x_4507_);
    return v___x_4509_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__3() -> *mut LeanObject {
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    v___x_4510_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__2_once),
        _init_l_Lake_Toml_arrayTable___closed__2,
    );
    v___x_4511_ = l_Lean_Parser_atomic(v___x_4510_);
    return v___x_4511_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__4() -> *mut LeanObject {
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    v___x_4512_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__18_once),
        _init_l_Lake_Toml_stdTable___closed__18,
    );
    v___x_4513_ = l_Lean_Parser_andthen(v___x_4512_, v___x_4512_);
    return v___x_4513_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__5() -> *mut LeanObject {
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    v___x_4514_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__4_once),
        _init_l_Lake_Toml_arrayTable___closed__4,
    );
    v___x_4515_ = l_Lake_Toml_trailingWs;
    v___x_4516_ = l_Lean_Parser_andthen(v___x_4515_, v___x_4514_);
    return v___x_4516_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__6() -> *mut LeanObject {
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    v___x_4517_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__5_once),
        _init_l_Lake_Toml_arrayTable___closed__5,
    );
    v___x_4518_ = l_Lake_Toml_key;
    v___x_4519_ = l_Lean_Parser_andthen(v___x_4518_, v___x_4517_);
    return v___x_4519_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__7() -> *mut LeanObject {
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    v___x_4520_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__6_once),
        _init_l_Lake_Toml_arrayTable___closed__6,
    );
    v___x_4521_ = l_Lake_Toml_trailingWs;
    v___x_4522_ = l_Lean_Parser_andthen(v___x_4521_, v___x_4520_);
    return v___x_4522_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__8() -> *mut LeanObject {
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    v___x_4523_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__7_once),
        _init_l_Lake_Toml_arrayTable___closed__7,
    );
    v___x_4524_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__3_once),
        _init_l_Lake_Toml_arrayTable___closed__3,
    );
    v___x_4525_ = l_Lean_Parser_andthen(v___x_4524_, v___x_4523_);
    return v___x_4525_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable___closed__9() -> *mut LeanObject {
    let mut v___x_4526_: u8 = 0;
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    v___x_4526_ = 0;
    v___x_4527_ = lean_obj_once(
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
pub unsafe fn _init_l_Lake_Toml_arrayTable() -> *mut LeanObject {
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    v___x_4531_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable___closed__9_once),
        _init_l_Lake_Toml_arrayTable___closed__9,
    );
    return v___x_4531_;
}
pub unsafe fn _init_l_Lake_Toml_table___closed__0() -> *mut LeanObject {
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    v___x_4532_ = l_Lake_Toml_arrayTable;
    v___x_4533_ = l_Lake_Toml_stdTable;
    v___x_4534_ = l_Lean_Parser_orelse(v___x_4533_, v___x_4532_);
    return v___x_4534_;
}
pub unsafe fn _init_l_Lake_Toml_table() -> *mut LeanObject {
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    v___x_4535_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_table___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_table___closed__0_once),
        _init_l_Lake_Toml_table___closed__0,
    );
    return v___x_4535_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2()
-> *mut LeanObject {
    let mut v___x_4541_: u32 = 0;
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    v___x_4541_ = 61;
    v___x_4542_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4543_ = lean_string_push(v___x_4542_, v___x_4541_);
    return v___x_4543_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3()
-> *mut LeanObject {
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    v___x_4544_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    v___x_4547_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4548_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    v___x_4550_ = lean_box(0);
    v___x_4551_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4,
    );
    v___x_4552_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4552_, 0, v___x_4551_);
    lean_ctor_set(v___x_4552_, 1, v___x_4550_);
    return v___x_4552_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6()
-> *mut LeanObject {
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: u32 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    v___x_4553_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4554_ = lean_obj_once(
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
    mut v_val_4557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: u8 = 0;
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    v___x_4558_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
    v___x_4559_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
    v___x_4560_ = l_Lake_Toml_key;
    v___x_4561_ = l_Lake_Toml_trailingWs;
    v___x_4562_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    v___x_4574_ = 1;
    v___x_4575_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1;
    v___x_4576_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0;
    v___x_4577_ = l_Lean_Parser_mkAntiquot(v___x_4576_, v___x_4575_, v___x_4574_, v___x_4574_);
    return v___x_4577_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(
    mut v_val_4578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    v___x_4579_ = lean_obj_once(
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
pub unsafe fn _init_l_Lake_Toml_header___closed__2() -> *mut LeanObject {
    let mut v___x_4589_: u8 = 0;
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
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
pub unsafe fn _init_l_Lake_Toml_header() -> *mut LeanObject {
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    v___x_4595_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_header___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_header___closed__2_once),
        _init_l_Lake_Toml_header___closed__2,
    );
    return v___x_4595_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5()
-> *mut LeanObject {
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    v___x_4605_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4;
    v___x_4606_ = l_Lean_Parser_symbol(v___x_4605_);
    return v___x_4606_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7()
-> *mut LeanObject {
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    v___x_4608_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6;
    v___x_4609_ = l_Lean_Parser_checkLinebreakBefore(v___x_4608_);
    return v___x_4609_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8()
-> *mut LeanObject {
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    v___x_4610_ = l_Lean_Parser_pushNone;
    v___x_4611_ = lean_obj_once(
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
    mut v_val_4613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: u8 = 0;
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    v___x_4614_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
    v___x_4615_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
    v___x_4616_ = l_Lake_Toml_header;
    v___x_4617_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v_val_4613_);
    v___x_4618_ = l_Lake_Toml_trailingSep;
    v___x_4619_ = l_Lean_Parser_andthen(v___x_4617_, v___x_4618_);
    v___x_4620_ = 1;
    v___x_4621_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3;
    v___x_4622_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5,
    );
    v_p_4623_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_4621_, v___x_4619_, v___x_4622_);
    v___x_4624_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: u32 = 0;
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    v___x_4637_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4638_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3;
    v___x_4639_ = 123;
    v___x_4640_ = l_Lake_Toml_chAtom(v___x_4639_, v___x_4638_, v___x_4637_);
    return v___x_4640_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6()
-> *mut LeanObject {
    let mut v___x_4642_: u32 = 0;
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    v___x_4642_ = 44;
    v___x_4643_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4644_ = lean_string_push(v___x_4643_, v___x_4642_);
    return v___x_4644_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7()
-> *mut LeanObject {
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    v___x_4645_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    v___x_4648_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4649_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    v___x_4651_ = lean_box(0);
    v___x_4652_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8,
    );
    v___x_4653_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4653_, 0, v___x_4652_);
    lean_ctor_set(v___x_4653_, 1, v___x_4651_);
    return v___x_4653_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10()
-> *mut LeanObject {
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u32 = 0;
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    v___x_4654_ = lean_alloc_closure(l_Lake_Toml_wsFn___boxed as *mut core::ffi::c_void, 2, 0);
    v___x_4655_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4658_: u32 = 0;
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    v___x_4658_ = 125;
    v___x_4659_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
    v___x_4660_ = lean_string_push(v___x_4659_, v___x_4658_);
    return v___x_4660_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12()
-> *mut LeanObject {
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    v___x_4661_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    v___x_4664_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
    v___x_4665_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    v___x_4667_ = lean_box(0);
    v___x_4668_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13,
    );
    v___x_4669_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4669_, 0, v___x_4668_);
    lean_ctor_set(v___x_4669_, 1, v___x_4667_);
    return v___x_4669_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15()
-> *mut LeanObject {
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: u32 = 0;
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    v___x_4670_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4671_ = lean_obj_once(
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
    mut v_val_4674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: u8 = 0;
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    v___x_4675_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0;
    v___x_4676_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1;
    v___x_4677_ = lean_obj_once(
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
    v___x_4682_ = lean_obj_once(
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
    v___x_4685_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: u32 = 0;
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    v___x_4697_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4698_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2;
    v___x_4699_ = 91;
    v___x_4700_ = l_Lake_Toml_chAtom(v___x_4699_, v___x_4698_, v___x_4697_);
    return v___x_4700_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4()
-> *mut LeanObject {
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: u32 = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    v___x_4701_ = l_Lake_Toml_trailingSep___closed__0;
    v___x_4702_ = lean_obj_once(
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
    mut v_val_4705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: u8 = 0;
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    v___x_4706_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0;
    v___x_4707_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1;
    v___x_4708_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3,
    );
    v___x_4709_ = l_Lake_Toml_trailingSep;
    v___x_4710_ = l_Lean_Parser_andthen(v_val_4705_, v___x_4709_);
    v___x_4711_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5;
    v___x_4712_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4,
    );
    v___x_4713_ = 1;
    v___x_4714_ = l_Lean_Parser_sepBy(v___x_4710_, v___x_4711_, v___x_4712_, v___x_4713_);
    v___x_4715_ = lean_obj_once(
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
pub unsafe fn _init_l_Lake_Toml_string___closed__3() -> *mut LeanObject {
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    v___x_4728_ = l_Lake_Toml_literalString;
    v___x_4729_ = l_Lake_Toml_mlLiteralString;
    v___x_4730_ = l_Lean_Parser_orelse(v___x_4729_, v___x_4728_);
    return v___x_4730_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__4() -> *mut LeanObject {
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    v___x_4731_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__3_once),
        _init_l_Lake_Toml_string___closed__3,
    );
    v___x_4732_ = l_Lake_Toml_basicString;
    v___x_4733_ = l_Lean_Parser_orelse(v___x_4732_, v___x_4731_);
    return v___x_4733_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__5() -> *mut LeanObject {
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    v___x_4734_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__4_once),
        _init_l_Lake_Toml_string___closed__4,
    );
    v___x_4735_ = l_Lake_Toml_mlBasicString;
    v___x_4736_ = l_Lean_Parser_orelse(v___x_4735_, v___x_4734_);
    return v___x_4736_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__6() -> *mut LeanObject {
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    v___x_4737_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__5_once),
        _init_l_Lake_Toml_string___closed__5,
    );
    v___x_4738_ = l_Lake_Toml_string___closed__2;
    v___x_4739_ = l_Lean_Parser_setExpected(v___x_4738_, v___x_4737_);
    return v___x_4739_;
}
pub unsafe fn _init_l_Lake_Toml_string___closed__7() -> *mut LeanObject {
    let mut v___x_4740_: u8 = 0;
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    v___x_4740_ = 0;
    v___x_4741_ = lean_obj_once(
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
pub unsafe fn _init_l_Lake_Toml_string() -> *mut LeanObject {
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    v___x_4745_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_string___closed__7_once),
        _init_l_Lake_Toml_string___closed__7,
    );
    return v___x_4745_;
}
pub unsafe fn _init_l_Lake_Toml_true___closed__5() -> *mut LeanObject {
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    v___x_4758_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4759_ = l_Lake_Toml_true___closed__4;
    v___x_4760_ = l_Lake_Toml_true___closed__1;
    v___x_4761_ = l_Lake_Toml_lit(v___x_4760_, v___x_4759_, v___x_4758_);
    return v___x_4761_;
}
pub unsafe fn _init_l_Lake_Toml_true() -> *mut LeanObject {
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    v___x_4762_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_true___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_true___closed__5_once),
        _init_l_Lake_Toml_true___closed__5,
    );
    return v___x_4762_;
}
pub unsafe fn _init_l_Lake_Toml_false___closed__5() -> *mut LeanObject {
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    v___x_4775_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_4776_ = l_Lake_Toml_false___closed__4;
    v___x_4777_ = l_Lake_Toml_false___closed__1;
    v___x_4778_ = l_Lake_Toml_lit(v___x_4777_, v___x_4776_, v___x_4775_);
    return v___x_4778_;
}
pub unsafe fn _init_l_Lake_Toml_false() -> *mut LeanObject {
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    v___x_4779_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_false___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_false___closed__5_once),
        _init_l_Lake_Toml_false___closed__5,
    );
    return v___x_4779_;
}
pub unsafe fn _init_l_Lake_Toml_boolean___closed__2() -> *mut LeanObject {
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    v___x_4785_ = l_Lake_Toml_false;
    v___x_4786_ = l_Lake_Toml_true;
    v___x_4787_ = l_Lean_Parser_orelse(v___x_4786_, v___x_4785_);
    return v___x_4787_;
}
pub unsafe fn _init_l_Lake_Toml_boolean___closed__3() -> *mut LeanObject {
    let mut v___x_4788_: u8 = 0;
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    v___x_4788_ = 0;
    v___x_4789_ = lean_obj_once(
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
pub unsafe fn _init_l_Lake_Toml_boolean() -> *mut LeanObject {
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    v___x_4793_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_boolean___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_boolean___closed__3_once),
        _init_l_Lake_Toml_boolean___closed__3,
    );
    return v___x_4793_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__0() -> *mut LeanObject {
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    v___x_4794_ = 0;
    v___x_4795_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
    v___x_4796_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
    v___x_4797_ = l_Lean_Parser_mkAntiquot(v___x_4796_, v___x_4795_, v___x_4794_, v___x_4794_);
    return v___x_4797_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__1() -> *mut LeanObject {
    let mut v___x_4798_: u8 = 0;
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    v___x_4798_ = 0;
    v___x_4799_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
    v___x_4800_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5;
    v___x_4801_ = l_Lean_Parser_mkAntiquot(v___x_4800_, v___x_4799_, v___x_4798_, v___x_4798_);
    return v___x_4801_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__2() -> *mut LeanObject {
    let mut v___x_4802_: u8 = 0;
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    v___x_4802_ = 0;
    v___x_4803_ = l_Lake_Toml_numeralFn___lam__0___closed__17;
    v___x_4804_ = l_Lake_Toml_numeralFn___lam__0___closed__16;
    v___x_4805_ = l_Lean_Parser_mkAntiquot(v___x_4804_, v___x_4803_, v___x_4802_, v___x_4802_);
    return v___x_4805_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__3() -> *mut LeanObject {
    let mut v___x_4806_: u8 = 0;
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    v___x_4806_ = 0;
    v___x_4807_ = l_Lake_Toml_numeralFn___lam__0___closed__12;
    v___x_4808_ = l_Lake_Toml_numeralFn___lam__0___closed__11;
    v___x_4809_ = l_Lean_Parser_mkAntiquot(v___x_4808_, v___x_4807_, v___x_4806_, v___x_4806_);
    return v___x_4809_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__4() -> *mut LeanObject {
    let mut v___x_4810_: u8 = 0;
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    v___x_4810_ = 0;
    v___x_4811_ = l_Lake_Toml_numeralFn___lam__0___closed__7;
    v___x_4812_ = l_Lake_Toml_numeralFn___lam__0___closed__6;
    v___x_4813_ = l_Lean_Parser_mkAntiquot(v___x_4812_, v___x_4811_, v___x_4810_, v___x_4810_);
    return v___x_4813_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__5() -> *mut LeanObject {
    let mut v___x_4814_: u8 = 0;
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    v___x_4814_ = 0;
    v___x_4815_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
    v___x_4816_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0;
    v___x_4817_ = l_Lean_Parser_mkAntiquot(v___x_4816_, v___x_4815_, v___x_4814_, v___x_4814_);
    return v___x_4817_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__8() -> *mut LeanObject {
    let mut v___x_4823_: u8 = 0;
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    v___x_4823_ = 1;
    v___x_4824_ = l_Lake_Toml_numeralAntiquot___closed__7;
    v___x_4825_ = l_Lake_Toml_numeralAntiquot___closed__6;
    v___x_4826_ = l_Lean_Parser_mkAntiquot(v___x_4825_, v___x_4824_, v___x_4823_, v___x_4823_);
    return v___x_4826_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__9() -> *mut LeanObject {
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    v___x_4827_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__8_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__8,
    );
    v___x_4828_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__5_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__5,
    );
    v___x_4829_ = l_Lean_Parser_orelse(v___x_4828_, v___x_4827_);
    return v___x_4829_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__10() -> *mut LeanObject {
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    v___x_4830_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__9),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__9_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__9,
    );
    v___x_4831_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__4_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__4,
    );
    v___x_4832_ = l_Lean_Parser_orelse(v___x_4831_, v___x_4830_);
    return v___x_4832_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__11() -> *mut LeanObject {
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    v___x_4833_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__10),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__10_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__10,
    );
    v___x_4834_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__3_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__3,
    );
    v___x_4835_ = l_Lean_Parser_orelse(v___x_4834_, v___x_4833_);
    return v___x_4835_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__12() -> *mut LeanObject {
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    v___x_4836_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__11),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__11_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__11,
    );
    v___x_4837_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__2_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__2,
    );
    v___x_4838_ = l_Lean_Parser_orelse(v___x_4837_, v___x_4836_);
    return v___x_4838_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__13() -> *mut LeanObject {
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    v___x_4839_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__12),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__12_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__12,
    );
    v___x_4840_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__1_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__1,
    );
    v___x_4841_ = l_Lean_Parser_orelse(v___x_4840_, v___x_4839_);
    return v___x_4841_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot___closed__14() -> *mut LeanObject {
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    v___x_4842_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__13),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__13_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__13,
    );
    v___x_4843_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__0_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__0,
    );
    v___x_4844_ = l_Lean_Parser_orelse(v___x_4843_, v___x_4842_);
    return v___x_4844_;
}
pub unsafe fn _init_l_Lake_Toml_numeralAntiquot() -> *mut LeanObject {
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    v___x_4845_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__14),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeralAntiquot___closed__14_once),
        _init_l_Lake_Toml_numeralAntiquot___closed__14,
    );
    return v___x_4845_;
}
pub unsafe fn _init_l_Lake_Toml_numeral___closed__0() -> *mut LeanObject {
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    v___x_4846_ = lean_alloc_closure(l_Lake_Toml_numeralFn as *mut core::ffi::c_void, 2, 0);
    v___x_4847_ = l_Lake_Toml_dynamicNode(v___x_4846_);
    return v___x_4847_;
}
pub unsafe fn _init_l_Lake_Toml_numeral___closed__1() -> *mut LeanObject {
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    v___x_4848_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeral___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeral___closed__0_once),
        _init_l_Lake_Toml_numeral___closed__0,
    );
    v___x_4849_ = l_Lake_Toml_numeralAntiquot;
    v___x_4850_ = l_Lean_Parser_withAntiquot(v___x_4849_, v___x_4848_);
    return v___x_4850_;
}
pub unsafe fn _init_l_Lake_Toml_numeral() -> *mut LeanObject {
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    v___x_4851_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_numeral___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_numeral___closed__1_once),
        _init_l_Lake_Toml_numeral___closed__1,
    );
    return v___x_4851_;
}
pub unsafe fn l_Lake_Toml_numeralOfKind___lam__0(
    mut v_kind_4852_: *mut LeanObject,
    mut v_x_4853_: *mut LeanObject,
) -> u8 {
    let mut v___x_4854_: u8 = 0;
    v___x_4854_ = l_Lean_Syntax_isOfKind(v_x_4853_, v_kind_4852_);
    return v___x_4854_;
}
pub unsafe fn l_Lake_Toml_numeralOfKind___lam__0___boxed(
    mut v_kind_4855_: *mut LeanObject,
    mut v_x_4856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4857_: u8 = 0;
    let mut v_r_4858_: *mut LeanObject = core::ptr::null_mut();
    v_res_4857_ = l_Lake_Toml_numeralOfKind___lam__0(v_kind_4855_, v_x_4856_);
    lean_dec(v_kind_4855_);
    v_r_4858_ = lean_box((v_res_4857_) as usize);
    return v_r_4858_;
}
pub unsafe fn l_Lake_Toml_numeralOfKind(
    mut v_name_4860_: *mut LeanObject,
    mut v_kind_4861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    v___f_4862_ = lean_alloc_closure(
        l_Lake_Toml_numeralOfKind___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4862_, 0, v_kind_4861_);
    v___x_4863_ = l_Lake_Toml_numeral;
    v___x_4864_ = lean_box(0);
    v___x_4865_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4865_, 0, v_name_4860_);
    lean_ctor_set(v___x_4865_, 1, v___x_4864_);
    v___x_4866_ = l_Lake_Toml_numeralOfKind___closed__0;
    v___x_4867_ = l_Lean_Parser_checkStackTop(v___f_4862_, v___x_4866_);
    v___x_4868_ = l_Lean_Parser_setExpected(v___x_4865_, v___x_4867_);
    v___x_4869_ = l_Lean_Parser_andthen(v___x_4863_, v___x_4868_);
    return v___x_4869_;
}
pub unsafe fn _init_l_Lake_Toml_float___closed__0() -> *mut LeanObject {
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    v___x_4870_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
    v___x_4871_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
    v___x_4872_ = l_Lake_Toml_numeralOfKind(v___x_4871_, v___x_4870_);
    return v___x_4872_;
}
pub unsafe fn _init_l_Lake_Toml_float() -> *mut LeanObject {
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    v___x_4873_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_float___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_float___closed__0_once),
        _init_l_Lake_Toml_float___closed__0,
    );
    return v___x_4873_;
}
pub unsafe fn _init_l_Lake_Toml_decInt___closed__0() -> *mut LeanObject {
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    v___x_4874_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
    v___x_4875_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0;
    v___x_4876_ = l_Lake_Toml_numeralOfKind(v___x_4875_, v___x_4874_);
    return v___x_4876_;
}
pub unsafe fn _init_l_Lake_Toml_decInt() -> *mut LeanObject {
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    v___x_4877_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_decInt___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_decInt___closed__0_once),
        _init_l_Lake_Toml_decInt___closed__0,
    );
    return v___x_4877_;
}
pub unsafe fn _init_l_Lake_Toml_binNum___closed__1() -> *mut LeanObject {
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    v___x_4879_ = l_Lake_Toml_numeralFn___lam__0___closed__17;
    v___x_4880_ = l_Lake_Toml_binNum___closed__0;
    v___x_4881_ = l_Lake_Toml_numeralOfKind(v___x_4880_, v___x_4879_);
    return v___x_4881_;
}
pub unsafe fn _init_l_Lake_Toml_binNum() -> *mut LeanObject {
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    v___x_4882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_binNum___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_binNum___closed__1_once),
        _init_l_Lake_Toml_binNum___closed__1,
    );
    return v___x_4882_;
}
pub unsafe fn _init_l_Lake_Toml_octNum___closed__1() -> *mut LeanObject {
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    v___x_4884_ = l_Lake_Toml_numeralFn___lam__0___closed__12;
    v___x_4885_ = l_Lake_Toml_octNum___closed__0;
    v___x_4886_ = l_Lake_Toml_numeralOfKind(v___x_4885_, v___x_4884_);
    return v___x_4886_;
}
pub unsafe fn _init_l_Lake_Toml_octNum() -> *mut LeanObject {
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    v___x_4887_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_octNum___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_octNum___closed__1_once),
        _init_l_Lake_Toml_octNum___closed__1,
    );
    return v___x_4887_;
}
pub unsafe fn _init_l_Lake_Toml_hexNum___closed__1() -> *mut LeanObject {
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    v___x_4889_ = l_Lake_Toml_numeralFn___lam__0___closed__7;
    v___x_4890_ = l_Lake_Toml_hexNum___closed__0;
    v___x_4891_ = l_Lake_Toml_numeralOfKind(v___x_4890_, v___x_4889_);
    return v___x_4891_;
}
pub unsafe fn _init_l_Lake_Toml_hexNum() -> *mut LeanObject {
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    v___x_4892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_hexNum___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_hexNum___closed__1_once),
        _init_l_Lake_Toml_hexNum___closed__1,
    );
    return v___x_4892_;
}
pub unsafe fn _init_l_Lake_Toml_dateTime___closed__0() -> *mut LeanObject {
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    v___x_4893_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
    v___x_4894_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2;
    v___x_4895_ = l_Lake_Toml_numeralOfKind(v___x_4894_, v___x_4893_);
    return v___x_4895_;
}
pub unsafe fn _init_l_Lake_Toml_dateTime() -> *mut LeanObject {
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    v___x_4896_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_dateTime___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_dateTime___closed__0_once),
        _init_l_Lake_Toml_dateTime___closed__0,
    );
    return v___x_4896_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(
    mut v_val_4897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    v___x_4898_ = l_Lake_Toml_string;
    v___x_4899_ = l_Lake_Toml_boolean;
    v___x_4900_ = l_Lake_Toml_numeral;
    lean_inc_ref(v_val_4897_);
    v___x_4901_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v_val_4897_);
    v___x_4902_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v_val_4897_);
    v___x_4903_ = l_Lean_Parser_orelse(v___x_4901_, v___x_4902_);
    v___x_4904_ = l_Lean_Parser_orelse(v___x_4900_, v___x_4903_);
    v___x_4905_ = l_Lean_Parser_orelse(v___x_4899_, v___x_4904_);
    v___x_4906_ = l_Lean_Parser_orelse(v___x_4898_, v___x_4905_);
    return v___x_4906_;
}
pub unsafe fn _init_l_Lake_Toml_val___closed__3() -> *mut LeanObject {
    let mut v___x_4913_: u8 = 0;
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    v___x_4913_ = 1;
    v___x_4914_ = l_Lake_Toml_val___closed__2;
    v___x_4915_ = l_Lake_Toml_val___closed__1;
    v___x_4916_ = l_Lake_Toml_val___closed__0;
    v___x_4917_ =
        l_Lake_Toml_recNodeWithAntiquot(v___x_4916_, v___x_4915_, v___x_4914_, v___x_4913_);
    return v___x_4917_;
}
pub unsafe fn _init_l_Lake_Toml_val() -> *mut LeanObject {
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    v___x_4918_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_val___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_val___closed__3_once),
        _init_l_Lake_Toml_val___closed__3,
    );
    return v___x_4918_;
}
pub unsafe fn _init_l_Lake_Toml_array___closed__0() -> *mut LeanObject {
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    v___x_4919_ = l_Lake_Toml_val;
    v___x_4920_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v___x_4919_);
    return v___x_4920_;
}
pub unsafe fn _init_l_Lake_Toml_array() -> *mut LeanObject {
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    v___x_4921_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_array___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_array___closed__0_once),
        _init_l_Lake_Toml_array___closed__0,
    );
    return v___x_4921_;
}
pub unsafe fn _init_l_Lake_Toml_inlineTable___closed__0() -> *mut LeanObject {
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    v___x_4922_ = l_Lake_Toml_val;
    v___x_4923_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v___x_4922_);
    return v___x_4923_;
}
pub unsafe fn _init_l_Lake_Toml_inlineTable() -> *mut LeanObject {
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    v___x_4924_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_inlineTable___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_inlineTable___closed__0_once),
        _init_l_Lake_Toml_inlineTable___closed__0,
    );
    return v___x_4924_;
}
pub unsafe fn _init_l_Lake_Toml_keyval___closed__0() -> *mut LeanObject {
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    v___x_4925_ = l_Lake_Toml_val;
    v___x_4926_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v___x_4925_);
    return v___x_4926_;
}
pub unsafe fn _init_l_Lake_Toml_keyval() -> *mut LeanObject {
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    v___x_4927_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_keyval___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_keyval___closed__0_once),
        _init_l_Lake_Toml_keyval___closed__0,
    );
    return v___x_4927_;
}
pub unsafe fn _init_l_Lake_Toml_expression___closed__0() -> *mut LeanObject {
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    v___x_4928_ = l_Lake_Toml_val;
    v___x_4929_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v___x_4928_);
    return v___x_4929_;
}
pub unsafe fn _init_l_Lake_Toml_expression() -> *mut LeanObject {
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    v___x_4930_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_expression___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_expression___closed__0_once),
        _init_l_Lake_Toml_expression___closed__0,
    );
    return v___x_4930_;
}
pub unsafe fn l_Lake_Toml_header_formatter(
    mut v_a_4931_: *mut LeanObject,
    mut v_a_4932_: *mut LeanObject,
    mut v_a_4933_: *mut LeanObject,
    mut v_a_4934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: u8 = 0;
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4940_: *mut LeanObject,
    mut v_a_4941_: *mut LeanObject,
    mut v_a_4942_: *mut LeanObject,
    mut v_a_4943_: *mut LeanObject,
    mut v_a_4944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4945_: *mut LeanObject = core::ptr::null_mut();
    v_res_4945_ = l_Lake_Toml_header_formatter(v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
    lean_dec(v_a_4943_);
    lean_dec_ref(v_a_4942_);
    lean_dec(v_a_4941_);
    lean_dec_ref(v_a_4940_);
    return v_res_4945_;
}
pub unsafe fn l_Lake_Toml_unquotedKey_formatter(
    mut v_a_4946_: *mut LeanObject,
    mut v_a_4947_: *mut LeanObject,
    mut v_a_4948_: *mut LeanObject,
    mut v_a_4949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: u8 = 0;
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4955_: *mut LeanObject,
    mut v_a_4956_: *mut LeanObject,
    mut v_a_4957_: *mut LeanObject,
    mut v_a_4958_: *mut LeanObject,
    mut v_a_4959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4960_: *mut LeanObject = core::ptr::null_mut();
    v_res_4960_ = l_Lake_Toml_unquotedKey_formatter(v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_);
    lean_dec(v_a_4958_);
    lean_dec_ref(v_a_4957_);
    lean_dec(v_a_4956_);
    lean_dec_ref(v_a_4955_);
    return v_res_4960_;
}
pub unsafe fn l_Lake_Toml_basicString_formatter(
    mut v_a_4961_: *mut LeanObject,
    mut v_a_4962_: *mut LeanObject,
    mut v_a_4963_: *mut LeanObject,
    mut v_a_4964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4970_: *mut LeanObject,
    mut v_a_4971_: *mut LeanObject,
    mut v_a_4972_: *mut LeanObject,
    mut v_a_4973_: *mut LeanObject,
    mut v_a_4974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4975_: *mut LeanObject = core::ptr::null_mut();
    v_res_4975_ = l_Lake_Toml_basicString_formatter(v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_);
    lean_dec(v_a_4973_);
    lean_dec_ref(v_a_4972_);
    lean_dec(v_a_4971_);
    lean_dec_ref(v_a_4970_);
    return v_res_4975_;
}
pub unsafe fn l_Lake_Toml_literalString_formatter(
    mut v_a_4976_: *mut LeanObject,
    mut v_a_4977_: *mut LeanObject,
    mut v_a_4978_: *mut LeanObject,
    mut v_a_4979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: u8 = 0;
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4985_: *mut LeanObject,
    mut v_a_4986_: *mut LeanObject,
    mut v_a_4987_: *mut LeanObject,
    mut v_a_4988_: *mut LeanObject,
    mut v_a_4989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4990_: *mut LeanObject = core::ptr::null_mut();
    v_res_4990_ = l_Lake_Toml_literalString_formatter(v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
    lean_dec(v_a_4988_);
    lean_dec_ref(v_a_4987_);
    lean_dec(v_a_4986_);
    lean_dec_ref(v_a_4985_);
    return v_res_4990_;
}
pub unsafe fn l_Lake_Toml_quotedKey_formatter(
    mut v_a_4991_: *mut LeanObject,
    mut v_a_4992_: *mut LeanObject,
    mut v_a_4993_: *mut LeanObject,
    mut v_a_4994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    v___x_4996_ = lean_alloc_closure(
        l_Lake_Toml_basicString_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4997_ = lean_alloc_closure(
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
    mut v_a_4999_: *mut LeanObject,
    mut v_a_5000_: *mut LeanObject,
    mut v_a_5001_: *mut LeanObject,
    mut v_a_5002_: *mut LeanObject,
    mut v_a_5003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5004_: *mut LeanObject = core::ptr::null_mut();
    v_res_5004_ = l_Lake_Toml_quotedKey_formatter(v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
    lean_dec(v_a_5002_);
    lean_dec_ref(v_a_5001_);
    lean_dec(v_a_5000_);
    lean_dec_ref(v_a_4999_);
    return v_res_5004_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey_formatter___closed__0() -> *mut LeanObject {
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    v___x_5005_ = lean_alloc_closure(
        l_Lake_Toml_quotedKey_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5006_ = lean_alloc_closure(
        l_Lake_Toml_unquotedKey_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5007_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5007_, 0, v___x_5006_);
    lean_closure_set(v___x_5007_, 1, v___x_5005_);
    return v___x_5007_;
}
pub unsafe fn l_Lake_Toml_simpleKey_formatter(
    mut v_a_5008_: *mut LeanObject,
    mut v_a_5009_: *mut LeanObject,
    mut v_a_5010_: *mut LeanObject,
    mut v_a_5011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    v___x_5013_ = l_Lake_Toml_simpleKey___closed__0;
    v___x_5014_ = l_Lake_Toml_simpleKey___closed__1;
    v___x_5015_ = lean_obj_once(
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
    mut v_a_5018_: *mut LeanObject,
    mut v_a_5019_: *mut LeanObject,
    mut v_a_5020_: *mut LeanObject,
    mut v_a_5021_: *mut LeanObject,
    mut v_a_5022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5023_: *mut LeanObject = core::ptr::null_mut();
    v_res_5023_ = l_Lake_Toml_simpleKey_formatter(v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_);
    lean_dec(v_a_5021_);
    lean_dec_ref(v_a_5020_);
    lean_dec(v_a_5019_);
    lean_dec_ref(v_a_5018_);
    return v_res_5023_;
}
pub unsafe fn l_Lake_Toml_trailingWs_formatter___redArg() -> *mut LeanObject {
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    v___x_5025_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_5025_;
}
pub unsafe fn l_Lake_Toml_trailingWs_formatter___redArg___boxed(
    mut v_a_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5027_: *mut LeanObject = core::ptr::null_mut();
    v_res_5027_ = l_Lake_Toml_trailingWs_formatter___redArg();
    return v_res_5027_;
}
pub unsafe fn l_Lake_Toml_trailingWs_formatter(
    mut v_a_5028_: *mut LeanObject,
    mut v_a_5029_: *mut LeanObject,
    mut v_a_5030_: *mut LeanObject,
    mut v_a_5031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_5033_;
}
pub unsafe fn l_Lake_Toml_trailingWs_formatter___boxed(
    mut v_a_5034_: *mut LeanObject,
    mut v_a_5035_: *mut LeanObject,
    mut v_a_5036_: *mut LeanObject,
    mut v_a_5037_: *mut LeanObject,
    mut v_a_5038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5039_: *mut LeanObject = core::ptr::null_mut();
    v_res_5039_ = l_Lake_Toml_trailingWs_formatter(v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_);
    lean_dec(v_a_5037_);
    lean_dec_ref(v_a_5036_);
    lean_dec(v_a_5035_);
    lean_dec_ref(v_a_5034_);
    return v_res_5039_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1() -> *mut LeanObject {
    let mut v___x_5040_: u32 = 0;
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    v___x_5040_ = 46;
    v___x_5041_ = lean_box_uint32(v___x_5040_);
    return v___x_5041_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__0() -> *mut LeanObject {
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    v___x_5042_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5043_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7_once),
        _init_l_Lake_Toml_key___closed__7,
    );
    v___x_5044_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
    v___x_5045_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5045_, 0, v___x_5044_);
    lean_closure_set(v___x_5045_, 1, v___x_5043_);
    lean_closure_set(v___x_5045_, 2, v___x_5042_);
    return v___x_5045_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__1() -> *mut LeanObject {
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    v___x_5046_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5047_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__0_once),
        _init_l_Lake_Toml_key_formatter___closed__0,
    );
    v___x_5048_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5048_, 0, v___x_5047_);
    lean_closure_set(v___x_5048_, 1, v___x_5046_);
    return v___x_5048_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__2() -> *mut LeanObject {
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    v___x_5049_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__1_once),
        _init_l_Lake_Toml_key_formatter___closed__1,
    );
    v___x_5050_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5051_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5051_, 0, v___x_5050_);
    lean_closure_set(v___x_5051_, 1, v___x_5049_);
    return v___x_5051_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__3() -> *mut LeanObject {
    let mut v___x_5052_: u8 = 0;
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    v___x_5052_ = 0;
    v___x_5053_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__2_once),
        _init_l_Lake_Toml_key_formatter___closed__2,
    );
    v___x_5054_ = l_Lake_Toml_key___closed__3;
    v___x_5055_ = lean_alloc_closure(
        l_Lake_Toml_simpleKey_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5056_ = lean_box((v___x_5052_) as usize);
    v___x_5057_ = lean_alloc_closure(
        l_Lean_Parser_sepBy1_formatter___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_5057_, 0, v___x_5055_);
    lean_closure_set(v___x_5057_, 1, v___x_5054_);
    lean_closure_set(v___x_5057_, 2, v___x_5053_);
    lean_closure_set(v___x_5057_, 3, v___x_5056_);
    return v___x_5057_;
}
pub unsafe fn _init_l_Lake_Toml_key_formatter___closed__4() -> *mut LeanObject {
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    v___x_5058_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_formatter___closed__3_once),
        _init_l_Lake_Toml_key_formatter___closed__3,
    );
    v___x_5059_ = l_Lake_Toml_key___closed__2;
    v___x_5060_ = lean_alloc_closure(
        l_Lean_Parser_setExpected_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5060_, 0, v___x_5059_);
    lean_closure_set(v___x_5060_, 1, v___x_5058_);
    return v___x_5060_;
}
pub unsafe fn l_Lake_Toml_key_formatter(
    mut v_a_5061_: *mut LeanObject,
    mut v_a_5062_: *mut LeanObject,
    mut v_a_5063_: *mut LeanObject,
    mut v_a_5064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: u8 = 0;
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    v___x_5066_ = l_Lake_Toml_key___closed__0;
    v___x_5067_ = l_Lake_Toml_key___closed__1;
    v___x_5068_ = lean_obj_once(
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
    mut v_a_5071_: *mut LeanObject,
    mut v_a_5072_: *mut LeanObject,
    mut v_a_5073_: *mut LeanObject,
    mut v_a_5074_: *mut LeanObject,
    mut v_a_5075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5076_: *mut LeanObject = core::ptr::null_mut();
    v_res_5076_ = l_Lake_Toml_key_formatter(v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
    lean_dec(v_a_5074_);
    lean_dec_ref(v_a_5073_);
    lean_dec(v_a_5072_);
    lean_dec_ref(v_a_5071_);
    return v_res_5076_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_5077_: u32 = 0;
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    v___x_5077_ = 61;
    v___x_5078_ = lean_box_uint32(v___x_5077_);
    return v___x_5078_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0()
-> *mut LeanObject {
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    v___x_5079_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5080_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5,
    );
    v___x_5081_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
    v___x_5082_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5082_, 0, v___x_5081_);
    lean_closure_set(v___x_5082_, 1, v___x_5080_);
    lean_closure_set(v___x_5082_, 2, v___x_5079_);
    return v___x_5082_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(
    mut v_val_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: u8 = 0;
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    v___x_5089_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
    v___x_5090_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
    v___x_5091_ = lean_alloc_closure(
        l_Lake_Toml_key_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5092_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5093_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0,
    );
    lean_inc_ref(v___x_5092_);
    v___x_5094_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5094_, 0, v___x_5092_);
    lean_closure_set(v___x_5094_, 1, v_val_5083_);
    v___x_5095_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5095_, 0, v___x_5093_);
    lean_closure_set(v___x_5095_, 1, v___x_5094_);
    v___x_5096_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5096_, 0, v___x_5092_);
    lean_closure_set(v___x_5096_, 1, v___x_5095_);
    v___x_5097_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5097_, 0, v___x_5091_);
    lean_closure_set(v___x_5097_, 1, v___x_5096_);
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
    mut v_val_5100_: *mut LeanObject,
    mut v_a_5101_: *mut LeanObject,
    mut v_a_5102_: *mut LeanObject,
    mut v_a_5103_: *mut LeanObject,
    mut v_a_5104_: *mut LeanObject,
    mut v_a_5105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5106_: *mut LeanObject = core::ptr::null_mut();
    v_res_5106_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(
        v_val_5100_,
        v_a_5101_,
        v_a_5102_,
        v_a_5103_,
        v_a_5104_,
    );
    lean_dec(v_a_5104_);
    lean_dec_ref(v_a_5103_);
    lean_dec(v_a_5102_);
    lean_dec_ref(v_a_5101_);
    return v_res_5106_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1() -> *mut LeanObject
{
    let mut v___x_5107_: u32 = 0;
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    v___x_5107_ = 91;
    v___x_5108_ = lean_box_uint32(v___x_5107_);
    return v___x_5108_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__0() -> *mut LeanObject {
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    v___x_5109_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5110_ = l_Lake_Toml_stdTable___closed__3;
    v___x_5111_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
    v___x_5112_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5112_, 0, v___x_5111_);
    lean_closure_set(v___x_5112_, 1, v___x_5110_);
    lean_closure_set(v___x_5112_, 2, v___x_5109_);
    return v___x_5112_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__1() -> *mut LeanObject {
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    v___x_5113_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5114_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8_once),
        _init_l_Lake_Toml_stdTable___closed__8,
    );
    v___x_5115_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
    v___x_5116_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5116_, 0, v___x_5115_);
    lean_closure_set(v___x_5116_, 1, v___x_5114_);
    lean_closure_set(v___x_5116_, 2, v___x_5113_);
    return v___x_5116_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__2() -> *mut LeanObject {
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    v___x_5117_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__1_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__1,
    );
    v___x_5118_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5118_, 0, v___x_5117_);
    return v___x_5118_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__3() -> *mut LeanObject {
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    v___x_5119_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__2_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__2,
    );
    v___x_5120_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__0_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__0,
    );
    v___x_5121_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5121_, 0, v___x_5120_);
    lean_closure_set(v___x_5121_, 1, v___x_5119_);
    return v___x_5121_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__4() -> *mut LeanObject {
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    v___x_5122_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__3_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__3,
    );
    v___x_5123_ = lean_alloc_closure(
        l_Lean_Parser_atomic_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5123_, 0, v___x_5122_);
    return v___x_5123_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1() -> *mut LeanObject
{
    let mut v___x_5124_: u32 = 0;
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    v___x_5124_ = 93;
    v___x_5125_ = lean_box_uint32(v___x_5124_);
    return v___x_5125_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__5() -> *mut LeanObject {
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    v___x_5126_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5127_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17_once),
        _init_l_Lake_Toml_stdTable___closed__17,
    );
    v___x_5128_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
    v___x_5129_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5129_, 0, v___x_5128_);
    lean_closure_set(v___x_5129_, 1, v___x_5127_);
    lean_closure_set(v___x_5129_, 2, v___x_5126_);
    return v___x_5129_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__6() -> *mut LeanObject {
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    v___x_5130_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__5_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__5,
    );
    v___x_5131_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5132_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5132_, 0, v___x_5131_);
    lean_closure_set(v___x_5132_, 1, v___x_5130_);
    return v___x_5132_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__7() -> *mut LeanObject {
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    v___x_5133_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__6_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__6,
    );
    v___x_5134_ = lean_alloc_closure(
        l_Lake_Toml_key_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5135_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5135_, 0, v___x_5134_);
    lean_closure_set(v___x_5135_, 1, v___x_5133_);
    return v___x_5135_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__8() -> *mut LeanObject {
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    v___x_5136_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__7_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__7,
    );
    v___x_5137_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5138_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5138_, 0, v___x_5137_);
    lean_closure_set(v___x_5138_, 1, v___x_5136_);
    return v___x_5138_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_formatter___closed__9() -> *mut LeanObject {
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    v___x_5139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__8_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__8,
    );
    v___x_5140_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__4_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__4,
    );
    v___x_5141_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5141_, 0, v___x_5140_);
    lean_closure_set(v___x_5141_, 1, v___x_5139_);
    return v___x_5141_;
}
pub unsafe fn l_Lake_Toml_stdTable_formatter(
    mut v_a_5142_: *mut LeanObject,
    mut v_a_5143_: *mut LeanObject,
    mut v_a_5144_: *mut LeanObject,
    mut v_a_5145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    v___x_5147_ = l_Lake_Toml_stdTable___closed__0;
    v___x_5148_ = l_Lake_Toml_stdTable___closed__1;
    v___x_5149_ = lean_obj_once(
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
    mut v_a_5152_: *mut LeanObject,
    mut v_a_5153_: *mut LeanObject,
    mut v_a_5154_: *mut LeanObject,
    mut v_a_5155_: *mut LeanObject,
    mut v_a_5156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5157_: *mut LeanObject = core::ptr::null_mut();
    v_res_5157_ = l_Lake_Toml_stdTable_formatter(v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_);
    lean_dec(v_a_5155_);
    lean_dec_ref(v_a_5154_);
    lean_dec(v_a_5153_);
    lean_dec_ref(v_a_5152_);
    return v_res_5157_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__0() -> *mut LeanObject {
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    v___x_5158_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__1_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__1,
    );
    v___x_5159_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__0_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__0,
    );
    v___x_5160_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5160_, 0, v___x_5159_);
    lean_closure_set(v___x_5160_, 1, v___x_5158_);
    return v___x_5160_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__1() -> *mut LeanObject {
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    v___x_5161_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__0_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__0,
    );
    v___x_5162_ = lean_alloc_closure(
        l_Lean_Parser_atomic_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5162_, 0, v___x_5161_);
    return v___x_5162_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__2() -> *mut LeanObject {
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    v___x_5163_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_formatter___closed__5_once),
        _init_l_Lake_Toml_stdTable_formatter___closed__5,
    );
    v___x_5164_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5164_, 0, v___x_5163_);
    lean_closure_set(v___x_5164_, 1, v___x_5163_);
    return v___x_5164_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__3() -> *mut LeanObject {
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    v___x_5165_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__2_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__2,
    );
    v___x_5166_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5167_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5167_, 0, v___x_5166_);
    lean_closure_set(v___x_5167_, 1, v___x_5165_);
    return v___x_5167_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__4() -> *mut LeanObject {
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    v___x_5168_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__3_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__3,
    );
    v___x_5169_ = lean_alloc_closure(
        l_Lake_Toml_key_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5170_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5170_, 0, v___x_5169_);
    lean_closure_set(v___x_5170_, 1, v___x_5168_);
    return v___x_5170_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__5() -> *mut LeanObject {
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    v___x_5171_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__4_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__4,
    );
    v___x_5172_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5173_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5173_, 0, v___x_5172_);
    lean_closure_set(v___x_5173_, 1, v___x_5171_);
    return v___x_5173_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_formatter___closed__6() -> *mut LeanObject {
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    v___x_5174_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__5_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__5,
    );
    v___x_5175_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_formatter___closed__1_once),
        _init_l_Lake_Toml_arrayTable_formatter___closed__1,
    );
    v___x_5176_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5176_, 0, v___x_5175_);
    lean_closure_set(v___x_5176_, 1, v___x_5174_);
    return v___x_5176_;
}
pub unsafe fn l_Lake_Toml_arrayTable_formatter(
    mut v_a_5177_: *mut LeanObject,
    mut v_a_5178_: *mut LeanObject,
    mut v_a_5179_: *mut LeanObject,
    mut v_a_5180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: u8 = 0;
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    v___x_5182_ = l_Lake_Toml_arrayTable___closed__0;
    v___x_5183_ = l_Lake_Toml_arrayTable___closed__1;
    v___x_5184_ = lean_obj_once(
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
    mut v_a_5187_: *mut LeanObject,
    mut v_a_5188_: *mut LeanObject,
    mut v_a_5189_: *mut LeanObject,
    mut v_a_5190_: *mut LeanObject,
    mut v_a_5191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5192_: *mut LeanObject = core::ptr::null_mut();
    v_res_5192_ = l_Lake_Toml_arrayTable_formatter(v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
    lean_dec(v_a_5190_);
    lean_dec_ref(v_a_5189_);
    lean_dec(v_a_5188_);
    lean_dec_ref(v_a_5187_);
    return v_res_5192_;
}
pub unsafe fn l_Lake_Toml_table_formatter(
    mut v_a_5193_: *mut LeanObject,
    mut v_a_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
    mut v_a_5196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    v___x_5198_ = lean_alloc_closure(
        l_Lake_Toml_stdTable_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5199_ = lean_alloc_closure(
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
    mut v_a_5201_: *mut LeanObject,
    mut v_a_5202_: *mut LeanObject,
    mut v_a_5203_: *mut LeanObject,
    mut v_a_5204_: *mut LeanObject,
    mut v_a_5205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5206_: *mut LeanObject = core::ptr::null_mut();
    v_res_5206_ = l_Lake_Toml_table_formatter(v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
    lean_dec(v_a_5204_);
    lean_dec_ref(v_a_5203_);
    lean_dec(v_a_5202_);
    lean_dec_ref(v_a_5201_);
    return v_res_5206_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(
    mut v_val_5213_: *mut LeanObject,
    mut v_a_5214_: *mut LeanObject,
    mut v_a_5215_: *mut LeanObject,
    mut v_a_5216_: *mut LeanObject,
    mut v_a_5217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    v___x_5219_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0;
    v___x_5220_ = lean_alloc_closure(
        l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5220_, 0, v_val_5213_);
    v___x_5221_ = lean_alloc_closure(
        l_Lake_Toml_table_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5222_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5222_, 0, v___x_5220_);
    lean_closure_set(v___x_5222_, 1, v___x_5221_);
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
    mut v_val_5224_: *mut LeanObject,
    mut v_a_5225_: *mut LeanObject,
    mut v_a_5226_: *mut LeanObject,
    mut v_a_5227_: *mut LeanObject,
    mut v_a_5228_: *mut LeanObject,
    mut v_a_5229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5230_: *mut LeanObject = core::ptr::null_mut();
    v_res_5230_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(
        v_val_5224_,
        v_a_5225_,
        v_a_5226_,
        v_a_5227_,
        v_a_5228_,
    );
    lean_dec(v_a_5228_);
    lean_dec_ref(v_a_5227_);
    lean_dec(v_a_5226_);
    lean_dec_ref(v_a_5225_);
    return v_res_5230_;
}
pub unsafe fn l_Lake_Toml_trailingSep_formatter___redArg() -> *mut LeanObject {
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    v___x_5232_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_5232_;
}
pub unsafe fn l_Lake_Toml_trailingSep_formatter___redArg___boxed(
    mut v_a_5233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5234_: *mut LeanObject = core::ptr::null_mut();
    v_res_5234_ = l_Lake_Toml_trailingSep_formatter___redArg();
    return v_res_5234_;
}
pub unsafe fn l_Lake_Toml_trailingSep_formatter(
    mut v_a_5235_: *mut LeanObject,
    mut v_a_5236_: *mut LeanObject,
    mut v_a_5237_: *mut LeanObject,
    mut v_a_5238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    v___x_5240_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_5240_;
}
pub unsafe fn l_Lake_Toml_trailingSep_formatter___boxed(
    mut v_a_5241_: *mut LeanObject,
    mut v_a_5242_: *mut LeanObject,
    mut v_a_5243_: *mut LeanObject,
    mut v_a_5244_: *mut LeanObject,
    mut v_a_5245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5246_: *mut LeanObject = core::ptr::null_mut();
    v_res_5246_ = l_Lake_Toml_trailingSep_formatter(v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_);
    lean_dec(v_a_5244_);
    lean_dec_ref(v_a_5243_);
    lean_dec(v_a_5242_);
    lean_dec_ref(v_a_5241_);
    return v_res_5246_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(
    mut v_val_5247_: *mut LeanObject,
    mut v_a_5248_: *mut LeanObject,
    mut v_a_5249_: *mut LeanObject,
    mut v_a_5250_: *mut LeanObject,
    mut v_a_5251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    v___x_5253_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
    v___x_5254_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
    v___x_5255_ = lean_alloc_closure(
        l_Lake_Toml_header_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5256_ = lean_alloc_closure(
        l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5256_, 0, v_val_5247_);
    v___x_5257_ = lean_alloc_closure(
        l_Lake_Toml_trailingSep_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5258_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5258_, 0, v___x_5256_);
    lean_closure_set(v___x_5258_, 1, v___x_5257_);
    v___x_5259_ = 1;
    v___x_5260_ = lean_box((v___x_5259_) as usize);
    v___x_5261_ = lean_alloc_closure(
        l_Lake_Toml_sepByLinebreak_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5261_, 0, v___x_5258_);
    lean_closure_set(v___x_5261_, 1, v___x_5260_);
    v___x_5262_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5262_, 0, v___x_5255_);
    lean_closure_set(v___x_5262_, 1, v___x_5261_);
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
    mut v_val_5264_: *mut LeanObject,
    mut v_a_5265_: *mut LeanObject,
    mut v_a_5266_: *mut LeanObject,
    mut v_a_5267_: *mut LeanObject,
    mut v_a_5268_: *mut LeanObject,
    mut v_a_5269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5270_: *mut LeanObject = core::ptr::null_mut();
    v_res_5270_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(
        v_val_5264_,
        v_a_5265_,
        v_a_5266_,
        v_a_5267_,
        v_a_5268_,
    );
    lean_dec(v_a_5268_);
    lean_dec_ref(v_a_5267_);
    lean_dec(v_a_5266_);
    lean_dec_ref(v_a_5265_);
    return v_res_5270_;
}
pub unsafe fn l_Lake_Toml_val_formatter(
    mut v_a_5271_: *mut LeanObject,
    mut v_a_5272_: *mut LeanObject,
    mut v_a_5273_: *mut LeanObject,
    mut v_a_5274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: u8 = 0;
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_5281_: *mut LeanObject,
    mut v_a_5282_: *mut LeanObject,
    mut v_a_5283_: *mut LeanObject,
    mut v_a_5284_: *mut LeanObject,
    mut v_a_5285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5286_: *mut LeanObject = core::ptr::null_mut();
    v_res_5286_ = l_Lake_Toml_val_formatter(v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
    lean_dec(v_a_5284_);
    lean_dec_ref(v_a_5283_);
    lean_dec(v_a_5282_);
    lean_dec_ref(v_a_5281_);
    return v_res_5286_;
}
pub unsafe fn l_Lake_Toml_toml_formatter(
    mut v_a_5287_: *mut LeanObject,
    mut v_a_5288_: *mut LeanObject,
    mut v_a_5289_: *mut LeanObject,
    mut v_a_5290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    v___x_5292_ = lean_alloc_closure(
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
    mut v_a_5294_: *mut LeanObject,
    mut v_a_5295_: *mut LeanObject,
    mut v_a_5296_: *mut LeanObject,
    mut v_a_5297_: *mut LeanObject,
    mut v_a_5298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5299_: *mut LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lake_Toml_toml_formatter(v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_);
    lean_dec(v_a_5297_);
    lean_dec_ref(v_a_5296_);
    lean_dec(v_a_5295_);
    lean_dec_ref(v_a_5294_);
    return v_res_5299_;
}
pub unsafe fn l_Lake_Toml_header_parenthesizer(
    mut v_a_5300_: *mut LeanObject,
    mut v_a_5301_: *mut LeanObject,
    mut v_a_5302_: *mut LeanObject,
    mut v_a_5303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: u8 = 0;
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_5309_: *mut LeanObject,
    mut v_a_5310_: *mut LeanObject,
    mut v_a_5311_: *mut LeanObject,
    mut v_a_5312_: *mut LeanObject,
    mut v_a_5313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5314_: *mut LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_Lake_Toml_header_parenthesizer(v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_);
    lean_dec(v_a_5312_);
    lean_dec_ref(v_a_5311_);
    lean_dec(v_a_5310_);
    lean_dec_ref(v_a_5309_);
    return v_res_5314_;
}
pub unsafe fn l_Lake_Toml_unquotedKey_parenthesizer(
    mut v_a_5315_: *mut LeanObject,
    mut v_a_5316_: *mut LeanObject,
    mut v_a_5317_: *mut LeanObject,
    mut v_a_5318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: u8 = 0;
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_5324_: *mut LeanObject,
    mut v_a_5325_: *mut LeanObject,
    mut v_a_5326_: *mut LeanObject,
    mut v_a_5327_: *mut LeanObject,
    mut v_a_5328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5329_: *mut LeanObject = core::ptr::null_mut();
    v_res_5329_ = l_Lake_Toml_unquotedKey_parenthesizer(v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_);
    lean_dec(v_a_5327_);
    lean_dec_ref(v_a_5326_);
    lean_dec(v_a_5325_);
    lean_dec_ref(v_a_5324_);
    return v_res_5329_;
}
pub unsafe fn l_Lake_Toml_basicString_parenthesizer(
    mut v_a_5330_: *mut LeanObject,
    mut v_a_5331_: *mut LeanObject,
    mut v_a_5332_: *mut LeanObject,
    mut v_a_5333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: u8 = 0;
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_5339_: *mut LeanObject,
    mut v_a_5340_: *mut LeanObject,
    mut v_a_5341_: *mut LeanObject,
    mut v_a_5342_: *mut LeanObject,
    mut v_a_5343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5344_: *mut LeanObject = core::ptr::null_mut();
    v_res_5344_ = l_Lake_Toml_basicString_parenthesizer(v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_);
    lean_dec(v_a_5342_);
    lean_dec_ref(v_a_5341_);
    lean_dec(v_a_5340_);
    lean_dec_ref(v_a_5339_);
    return v_res_5344_;
}
pub unsafe fn l_Lake_Toml_literalString_parenthesizer(
    mut v_a_5345_: *mut LeanObject,
    mut v_a_5346_: *mut LeanObject,
    mut v_a_5347_: *mut LeanObject,
    mut v_a_5348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: u8 = 0;
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_5354_: *mut LeanObject,
    mut v_a_5355_: *mut LeanObject,
    mut v_a_5356_: *mut LeanObject,
    mut v_a_5357_: *mut LeanObject,
    mut v_a_5358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5359_: *mut LeanObject = core::ptr::null_mut();
    v_res_5359_ =
        l_Lake_Toml_literalString_parenthesizer(v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_);
    lean_dec(v_a_5357_);
    lean_dec_ref(v_a_5356_);
    lean_dec(v_a_5355_);
    lean_dec_ref(v_a_5354_);
    return v_res_5359_;
}
pub unsafe fn l_Lake_Toml_quotedKey_parenthesizer(
    mut v_a_5360_: *mut LeanObject,
    mut v_a_5361_: *mut LeanObject,
    mut v_a_5362_: *mut LeanObject,
    mut v_a_5363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    v___x_5365_ = lean_alloc_closure(
        l_Lake_Toml_basicString_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5366_ = lean_alloc_closure(
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
    mut v_a_5368_: *mut LeanObject,
    mut v_a_5369_: *mut LeanObject,
    mut v_a_5370_: *mut LeanObject,
    mut v_a_5371_: *mut LeanObject,
    mut v_a_5372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5373_: *mut LeanObject = core::ptr::null_mut();
    v_res_5373_ = l_Lake_Toml_quotedKey_parenthesizer(v_a_5368_, v_a_5369_, v_a_5370_, v_a_5371_);
    lean_dec(v_a_5371_);
    lean_dec_ref(v_a_5370_);
    lean_dec(v_a_5369_);
    lean_dec_ref(v_a_5368_);
    return v_res_5373_;
}
pub unsafe fn _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0() -> *mut LeanObject {
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    v___x_5374_ = lean_alloc_closure(
        l_Lake_Toml_quotedKey_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5375_ = lean_alloc_closure(
        l_Lake_Toml_unquotedKey_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5376_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5376_, 0, v___x_5375_);
    lean_closure_set(v___x_5376_, 1, v___x_5374_);
    return v___x_5376_;
}
pub unsafe fn l_Lake_Toml_simpleKey_parenthesizer(
    mut v_a_5377_: *mut LeanObject,
    mut v_a_5378_: *mut LeanObject,
    mut v_a_5379_: *mut LeanObject,
    mut v_a_5380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: u8 = 0;
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    v___x_5382_ = l_Lake_Toml_simpleKey___closed__0;
    v___x_5383_ = l_Lake_Toml_simpleKey___closed__1;
    v___x_5384_ = lean_obj_once(
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
    mut v_a_5387_: *mut LeanObject,
    mut v_a_5388_: *mut LeanObject,
    mut v_a_5389_: *mut LeanObject,
    mut v_a_5390_: *mut LeanObject,
    mut v_a_5391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5392_: *mut LeanObject = core::ptr::null_mut();
    v_res_5392_ = l_Lake_Toml_simpleKey_parenthesizer(v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_);
    lean_dec(v_a_5390_);
    lean_dec_ref(v_a_5389_);
    lean_dec(v_a_5388_);
    lean_dec_ref(v_a_5387_);
    return v_res_5392_;
}
pub unsafe fn l_Lake_Toml_trailingWs_parenthesizer___redArg() -> *mut LeanObject {
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_5394_;
}
pub unsafe fn l_Lake_Toml_trailingWs_parenthesizer___redArg___boxed(
    mut v_a_5395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5396_: *mut LeanObject = core::ptr::null_mut();
    v_res_5396_ = l_Lake_Toml_trailingWs_parenthesizer___redArg();
    return v_res_5396_;
}
pub unsafe fn l_Lake_Toml_trailingWs_parenthesizer(
    mut v_a_5397_: *mut LeanObject,
    mut v_a_5398_: *mut LeanObject,
    mut v_a_5399_: *mut LeanObject,
    mut v_a_5400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    v___x_5402_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_5402_;
}
pub unsafe fn l_Lake_Toml_trailingWs_parenthesizer___boxed(
    mut v_a_5403_: *mut LeanObject,
    mut v_a_5404_: *mut LeanObject,
    mut v_a_5405_: *mut LeanObject,
    mut v_a_5406_: *mut LeanObject,
    mut v_a_5407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5408_: *mut LeanObject = core::ptr::null_mut();
    v_res_5408_ = l_Lake_Toml_trailingWs_parenthesizer(v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
    lean_dec(v_a_5406_);
    lean_dec_ref(v_a_5405_);
    lean_dec(v_a_5404_);
    lean_dec_ref(v_a_5403_);
    return v_res_5408_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__0() -> *mut LeanObject {
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    v___x_5409_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5410_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_key___closed__7_once),
        _init_l_Lake_Toml_key___closed__7,
    );
    v___x_5411_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
    v___x_5412_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5412_, 0, v___x_5411_);
    lean_closure_set(v___x_5412_, 1, v___x_5410_);
    lean_closure_set(v___x_5412_, 2, v___x_5409_);
    return v___x_5412_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__1() -> *mut LeanObject {
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    v___x_5413_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5414_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__0,
    );
    v___x_5415_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5415_, 0, v___x_5414_);
    lean_closure_set(v___x_5415_, 1, v___x_5413_);
    return v___x_5415_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__2() -> *mut LeanObject {
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    v___x_5416_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__1_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__1,
    );
    v___x_5417_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5418_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5418_, 0, v___x_5417_);
    lean_closure_set(v___x_5418_, 1, v___x_5416_);
    return v___x_5418_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__3() -> *mut LeanObject {
    let mut v___x_5419_: u8 = 0;
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    v___x_5419_ = 0;
    v___x_5420_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__2_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__2,
    );
    v___x_5421_ = l_Lake_Toml_key___closed__3;
    v___x_5422_ = lean_alloc_closure(
        l_Lake_Toml_simpleKey_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5423_ = lean_box((v___x_5419_) as usize);
    v___x_5424_ = lean_alloc_closure(
        l_Lean_Parser_sepBy1_parenthesizer___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_5424_, 0, v___x_5422_);
    lean_closure_set(v___x_5424_, 1, v___x_5421_);
    lean_closure_set(v___x_5424_, 2, v___x_5420_);
    lean_closure_set(v___x_5424_, 3, v___x_5423_);
    return v___x_5424_;
}
pub unsafe fn _init_l_Lake_Toml_key_parenthesizer___closed__4() -> *mut LeanObject {
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    v___x_5425_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_key_parenthesizer___closed__3_once),
        _init_l_Lake_Toml_key_parenthesizer___closed__3,
    );
    v___x_5426_ = l_Lake_Toml_key___closed__2;
    v___x_5427_ = lean_alloc_closure(
        l_Lean_Parser_setExpected_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5427_, 0, v___x_5426_);
    lean_closure_set(v___x_5427_, 1, v___x_5425_);
    return v___x_5427_;
}
pub unsafe fn l_Lake_Toml_key_parenthesizer(
    mut v_a_5428_: *mut LeanObject,
    mut v_a_5429_: *mut LeanObject,
    mut v_a_5430_: *mut LeanObject,
    mut v_a_5431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: u8 = 0;
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    v___x_5433_ = l_Lake_Toml_key___closed__0;
    v___x_5434_ = l_Lake_Toml_key___closed__1;
    v___x_5435_ = lean_obj_once(
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
    mut v_a_5438_: *mut LeanObject,
    mut v_a_5439_: *mut LeanObject,
    mut v_a_5440_: *mut LeanObject,
    mut v_a_5441_: *mut LeanObject,
    mut v_a_5442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5443_: *mut LeanObject = core::ptr::null_mut();
    v_res_5443_ = l_Lake_Toml_key_parenthesizer(v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_);
    lean_dec(v_a_5441_);
    lean_dec_ref(v_a_5440_);
    lean_dec(v_a_5439_);
    lean_dec_ref(v_a_5438_);
    return v_res_5443_;
}
pub unsafe fn _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0()
-> *mut LeanObject {
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    v___x_5444_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5445_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5,
    );
    v___x_5446_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
    v___x_5447_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5447_, 0, v___x_5446_);
    lean_closure_set(v___x_5447_, 1, v___x_5445_);
    lean_closure_set(v___x_5447_, 2, v___x_5444_);
    return v___x_5447_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(
    mut v_val_5448_: *mut LeanObject,
    mut v_a_5449_: *mut LeanObject,
    mut v_a_5450_: *mut LeanObject,
    mut v_a_5451_: *mut LeanObject,
    mut v_a_5452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: u8 = 0;
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    v___x_5454_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
    v___x_5455_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
    v___x_5456_ = lean_alloc_closure(
        l_Lake_Toml_key_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5457_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5458_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once
        ),
        _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0,
    );
    lean_inc_ref(v___x_5457_);
    v___x_5459_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5459_, 0, v___x_5457_);
    lean_closure_set(v___x_5459_, 1, v_val_5448_);
    v___x_5460_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5460_, 0, v___x_5458_);
    lean_closure_set(v___x_5460_, 1, v___x_5459_);
    v___x_5461_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5461_, 0, v___x_5457_);
    lean_closure_set(v___x_5461_, 1, v___x_5460_);
    v___x_5462_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5462_, 0, v___x_5456_);
    lean_closure_set(v___x_5462_, 1, v___x_5461_);
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
    mut v_val_5465_: *mut LeanObject,
    mut v_a_5466_: *mut LeanObject,
    mut v_a_5467_: *mut LeanObject,
    mut v_a_5468_: *mut LeanObject,
    mut v_a_5469_: *mut LeanObject,
    mut v_a_5470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5471_: *mut LeanObject = core::ptr::null_mut();
    v_res_5471_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(
        v_val_5465_,
        v_a_5466_,
        v_a_5467_,
        v_a_5468_,
        v_a_5469_,
    );
    lean_dec(v_a_5469_);
    lean_dec_ref(v_a_5468_);
    lean_dec(v_a_5467_);
    lean_dec_ref(v_a_5466_);
    return v_res_5471_;
}
pub unsafe fn l_Lake_Toml_stdTable_parenthesizer___lam__0(
    mut v___x_5472_: *mut LeanObject,
    mut v___x_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_5480_: *mut LeanObject,
    mut v___x_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
    mut v___y_5486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5487_: *mut LeanObject = core::ptr::null_mut();
    v_res_5487_ = l_Lake_Toml_stdTable_parenthesizer___lam__0(
        v___x_5480_,
        v___x_5481_,
        v___y_5482_,
        v___y_5483_,
        v___y_5484_,
        v___y_5485_,
    );
    lean_dec(v___y_5485_);
    lean_dec_ref(v___y_5484_);
    lean_dec(v___y_5483_);
    lean_dec_ref(v___y_5482_);
    return v_res_5487_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__0() -> *mut LeanObject {
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    v___x_5488_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5489_ = l_Lake_Toml_stdTable___closed__3;
    v___x_5490_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
    v___x_5491_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5491_, 0, v___x_5490_);
    lean_closure_set(v___x_5491_, 1, v___x_5489_);
    lean_closure_set(v___x_5491_, 2, v___x_5488_);
    return v___x_5491_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__1() -> *mut LeanObject {
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    v___x_5492_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5493_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__8_once),
        _init_l_Lake_Toml_stdTable___closed__8,
    );
    v___x_5494_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
    v___x_5495_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5495_, 0, v___x_5494_);
    lean_closure_set(v___x_5495_, 1, v___x_5493_);
    lean_closure_set(v___x_5495_, 2, v___x_5492_);
    return v___x_5495_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__2() -> *mut LeanObject {
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    v___x_5496_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__1_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__1,
    );
    v___x_5497_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5497_, 0, v___x_5496_);
    return v___x_5497_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__3() -> *mut LeanObject {
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5500_: *mut LeanObject = core::ptr::null_mut();
    v___x_5498_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__2_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__2,
    );
    v___x_5499_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__0,
    );
    v___f_5500_ = lean_alloc_closure(
        l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_5500_, 0, v___x_5499_);
    lean_closure_set(v___f_5500_, 1, v___x_5498_);
    return v___f_5500_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__4() -> *mut LeanObject {
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    v___x_5501_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
    v___x_5502_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable___closed__17_once),
        _init_l_Lake_Toml_stdTable___closed__17,
    );
    v___x_5503_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
    v___x_5504_ = lean_alloc_closure(
        l_Lake_Toml_chAtom_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_5504_, 0, v___x_5503_);
    lean_closure_set(v___x_5504_, 1, v___x_5502_);
    lean_closure_set(v___x_5504_, 2, v___x_5501_);
    return v___x_5504_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__5() -> *mut LeanObject {
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    v___x_5505_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__4_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__4,
    );
    v___x_5506_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5507_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5507_, 0, v___x_5506_);
    lean_closure_set(v___x_5507_, 1, v___x_5505_);
    return v___x_5507_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__6() -> *mut LeanObject {
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    v___x_5508_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__5_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__5,
    );
    v___x_5509_ = lean_alloc_closure(
        l_Lake_Toml_key_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5510_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5510_, 0, v___x_5509_);
    lean_closure_set(v___x_5510_, 1, v___x_5508_);
    return v___x_5510_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__7() -> *mut LeanObject {
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    v___x_5511_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__6_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__6,
    );
    v___x_5512_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5513_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5513_, 0, v___x_5512_);
    lean_closure_set(v___x_5513_, 1, v___x_5511_);
    return v___x_5513_;
}
pub unsafe fn _init_l_Lake_Toml_stdTable_parenthesizer___closed__8() -> *mut LeanObject {
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    v___x_5514_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__7_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__7,
    );
    v___f_5515_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__3_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__3,
    );
    v___x_5516_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5516_, 0, v___f_5515_);
    lean_closure_set(v___x_5516_, 1, v___x_5514_);
    return v___x_5516_;
}
pub unsafe fn l_Lake_Toml_stdTable_parenthesizer(
    mut v_a_5517_: *mut LeanObject,
    mut v_a_5518_: *mut LeanObject,
    mut v_a_5519_: *mut LeanObject,
    mut v_a_5520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: u8 = 0;
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    v___x_5522_ = l_Lake_Toml_stdTable___closed__0;
    v___x_5523_ = l_Lake_Toml_stdTable___closed__1;
    v___x_5524_ = lean_obj_once(
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
    mut v_a_5527_: *mut LeanObject,
    mut v_a_5528_: *mut LeanObject,
    mut v_a_5529_: *mut LeanObject,
    mut v_a_5530_: *mut LeanObject,
    mut v_a_5531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5532_: *mut LeanObject = core::ptr::null_mut();
    v_res_5532_ = l_Lake_Toml_stdTable_parenthesizer(v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_);
    lean_dec(v_a_5530_);
    lean_dec_ref(v_a_5529_);
    lean_dec(v_a_5528_);
    lean_dec_ref(v_a_5527_);
    return v_res_5532_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0() -> *mut LeanObject {
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5535_: *mut LeanObject = core::ptr::null_mut();
    v___x_5533_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__1_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__1,
    );
    v___x_5534_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__0,
    );
    v___f_5535_ = lean_alloc_closure(
        l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_5535_, 0, v___x_5534_);
    lean_closure_set(v___f_5535_, 1, v___x_5533_);
    return v___f_5535_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1() -> *mut LeanObject {
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    v___x_5536_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_stdTable_parenthesizer___closed__4_once),
        _init_l_Lake_Toml_stdTable_parenthesizer___closed__4,
    );
    v___x_5537_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5537_, 0, v___x_5536_);
    lean_closure_set(v___x_5537_, 1, v___x_5536_);
    return v___x_5537_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2() -> *mut LeanObject {
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    v___x_5538_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__1_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1,
    );
    v___x_5539_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5540_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5540_, 0, v___x_5539_);
    lean_closure_set(v___x_5540_, 1, v___x_5538_);
    return v___x_5540_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3() -> *mut LeanObject {
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    v___x_5541_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__2_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2,
    );
    v___x_5542_ = lean_alloc_closure(
        l_Lake_Toml_key_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5543_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5543_, 0, v___x_5542_);
    lean_closure_set(v___x_5543_, 1, v___x_5541_);
    return v___x_5543_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4() -> *mut LeanObject {
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    v___x_5544_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__3_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3,
    );
    v___x_5545_ = lean_alloc_closure(
        l_Lake_Toml_trailingWs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5546_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5546_, 0, v___x_5545_);
    lean_closure_set(v___x_5546_, 1, v___x_5544_);
    return v___x_5546_;
}
pub unsafe fn _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5() -> *mut LeanObject {
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    v___x_5547_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__4_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4,
    );
    v___f_5548_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_arrayTable_parenthesizer___closed__0_once),
        _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0,
    );
    v___x_5549_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5549_, 0, v___f_5548_);
    lean_closure_set(v___x_5549_, 1, v___x_5547_);
    return v___x_5549_;
}
pub unsafe fn l_Lake_Toml_arrayTable_parenthesizer(
    mut v_a_5550_: *mut LeanObject,
    mut v_a_5551_: *mut LeanObject,
    mut v_a_5552_: *mut LeanObject,
    mut v_a_5553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: u8 = 0;
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    v___x_5555_ = l_Lake_Toml_arrayTable___closed__0;
    v___x_5556_ = l_Lake_Toml_arrayTable___closed__1;
    v___x_5557_ = lean_obj_once(
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
    mut v_a_5560_: *mut LeanObject,
    mut v_a_5561_: *mut LeanObject,
    mut v_a_5562_: *mut LeanObject,
    mut v_a_5563_: *mut LeanObject,
    mut v_a_5564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5565_: *mut LeanObject = core::ptr::null_mut();
    v_res_5565_ = l_Lake_Toml_arrayTable_parenthesizer(v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_);
    lean_dec(v_a_5563_);
    lean_dec_ref(v_a_5562_);
    lean_dec(v_a_5561_);
    lean_dec_ref(v_a_5560_);
    return v_res_5565_;
}
pub unsafe fn l_Lake_Toml_table_parenthesizer(
    mut v_a_5566_: *mut LeanObject,
    mut v_a_5567_: *mut LeanObject,
    mut v_a_5568_: *mut LeanObject,
    mut v_a_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    v___x_5571_ = lean_alloc_closure(
        l_Lake_Toml_stdTable_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5572_ = lean_alloc_closure(
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
    mut v_a_5574_: *mut LeanObject,
    mut v_a_5575_: *mut LeanObject,
    mut v_a_5576_: *mut LeanObject,
    mut v_a_5577_: *mut LeanObject,
    mut v_a_5578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5579_: *mut LeanObject = core::ptr::null_mut();
    v_res_5579_ = l_Lake_Toml_table_parenthesizer(v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_);
    lean_dec(v_a_5577_);
    lean_dec_ref(v_a_5576_);
    lean_dec(v_a_5575_);
    lean_dec_ref(v_a_5574_);
    return v_res_5579_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(
    mut v_val_5586_: *mut LeanObject,
    mut v_a_5587_: *mut LeanObject,
    mut v_a_5588_: *mut LeanObject,
    mut v_a_5589_: *mut LeanObject,
    mut v_a_5590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    v___x_5592_ =
        l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0;
    v___x_5593_ = lean_alloc_closure(
        l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5593_, 0, v_val_5586_);
    v___x_5594_ = lean_alloc_closure(
        l_Lake_Toml_table_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5595_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5595_, 0, v___x_5593_);
    lean_closure_set(v___x_5595_, 1, v___x_5594_);
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
    mut v_val_5597_: *mut LeanObject,
    mut v_a_5598_: *mut LeanObject,
    mut v_a_5599_: *mut LeanObject,
    mut v_a_5600_: *mut LeanObject,
    mut v_a_5601_: *mut LeanObject,
    mut v_a_5602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5603_: *mut LeanObject = core::ptr::null_mut();
    v_res_5603_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(
        v_val_5597_,
        v_a_5598_,
        v_a_5599_,
        v_a_5600_,
        v_a_5601_,
    );
    lean_dec(v_a_5601_);
    lean_dec_ref(v_a_5600_);
    lean_dec(v_a_5599_);
    lean_dec_ref(v_a_5598_);
    return v_res_5603_;
}
pub unsafe fn l_Lake_Toml_trailingSep_parenthesizer___redArg() -> *mut LeanObject {
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    v___x_5605_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_5605_;
}
pub unsafe fn l_Lake_Toml_trailingSep_parenthesizer___redArg___boxed(
    mut v_a_5606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5607_: *mut LeanObject = core::ptr::null_mut();
    v_res_5607_ = l_Lake_Toml_trailingSep_parenthesizer___redArg();
    return v_res_5607_;
}
pub unsafe fn l_Lake_Toml_trailingSep_parenthesizer(
    mut v_a_5608_: *mut LeanObject,
    mut v_a_5609_: *mut LeanObject,
    mut v_a_5610_: *mut LeanObject,
    mut v_a_5611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    v___x_5613_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_5613_;
}
pub unsafe fn l_Lake_Toml_trailingSep_parenthesizer___boxed(
    mut v_a_5614_: *mut LeanObject,
    mut v_a_5615_: *mut LeanObject,
    mut v_a_5616_: *mut LeanObject,
    mut v_a_5617_: *mut LeanObject,
    mut v_a_5618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5619_: *mut LeanObject = core::ptr::null_mut();
    v_res_5619_ = l_Lake_Toml_trailingSep_parenthesizer(v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_);
    lean_dec(v_a_5617_);
    lean_dec_ref(v_a_5616_);
    lean_dec(v_a_5615_);
    lean_dec_ref(v_a_5614_);
    return v_res_5619_;
}
pub unsafe fn l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(
    mut v_val_5620_: *mut LeanObject,
    mut v_a_5621_: *mut LeanObject,
    mut v_a_5622_: *mut LeanObject,
    mut v_a_5623_: *mut LeanObject,
    mut v_a_5624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: u8 = 0;
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    v___x_5626_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
    v___x_5627_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
    v___x_5628_ = lean_alloc_closure(
        l_Lake_Toml_header_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5629_ = lean_alloc_closure(
        l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_5629_, 0, v_val_5620_);
    v___x_5630_ = lean_alloc_closure(
        l_Lake_Toml_trailingSep_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_5631_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5631_, 0, v___x_5629_);
    lean_closure_set(v___x_5631_, 1, v___x_5630_);
    v___x_5632_ = 1;
    v___x_5633_ = lean_box((v___x_5632_) as usize);
    v___x_5634_ = lean_alloc_closure(
        l_Lake_Toml_sepByLinebreak_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5634_, 0, v___x_5631_);
    lean_closure_set(v___x_5634_, 1, v___x_5633_);
    v___x_5635_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_5635_, 0, v___x_5628_);
    lean_closure_set(v___x_5635_, 1, v___x_5634_);
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
    mut v_val_5637_: *mut LeanObject,
    mut v_a_5638_: *mut LeanObject,
    mut v_a_5639_: *mut LeanObject,
    mut v_a_5640_: *mut LeanObject,
    mut v_a_5641_: *mut LeanObject,
    mut v_a_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5643_: *mut LeanObject = core::ptr::null_mut();
    v_res_5643_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(
        v_val_5637_,
        v_a_5638_,
        v_a_5639_,
        v_a_5640_,
        v_a_5641_,
    );
    lean_dec(v_a_5641_);
    lean_dec_ref(v_a_5640_);
    lean_dec(v_a_5639_);
    lean_dec_ref(v_a_5638_);
    return v_res_5643_;
}
pub unsafe fn l_Lake_Toml_val_parenthesizer(
    mut v_a_5644_: *mut LeanObject,
    mut v_a_5645_: *mut LeanObject,
    mut v_a_5646_: *mut LeanObject,
    mut v_a_5647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: u8 = 0;
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_5654_: *mut LeanObject,
    mut v_a_5655_: *mut LeanObject,
    mut v_a_5656_: *mut LeanObject,
    mut v_a_5657_: *mut LeanObject,
    mut v_a_5658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5659_: *mut LeanObject = core::ptr::null_mut();
    v_res_5659_ = l_Lake_Toml_val_parenthesizer(v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_);
    lean_dec(v_a_5657_);
    lean_dec_ref(v_a_5656_);
    lean_dec(v_a_5655_);
    lean_dec_ref(v_a_5654_);
    return v_res_5659_;
}
pub unsafe fn l_Lake_Toml_toml_parenthesizer(
    mut v_a_5660_: *mut LeanObject,
    mut v_a_5661_: *mut LeanObject,
    mut v_a_5662_: *mut LeanObject,
    mut v_a_5663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    v___x_5665_ = lean_alloc_closure(
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
    mut v_a_5667_: *mut LeanObject,
    mut v_a_5668_: *mut LeanObject,
    mut v_a_5669_: *mut LeanObject,
    mut v_a_5670_: *mut LeanObject,
    mut v_a_5671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5672_: *mut LeanObject = core::ptr::null_mut();
    v_res_5672_ = l_Lake_Toml_toml_parenthesizer(v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_);
    lean_dec(v_a_5670_);
    lean_dec_ref(v_a_5669_);
    lean_dec(v_a_5668_);
    lean_dec_ref(v_a_5667_);
    return v_res_5672_;
}
pub unsafe fn _init_l_Lake_Toml_toml___closed__0() -> *mut LeanObject {
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    v___x_5673_ = l_Lake_Toml_val;
    v___x_5674_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(v___x_5673_);
    return v___x_5674_;
}
pub unsafe fn _init_l_Lake_Toml_toml___closed__1() -> *mut LeanObject {
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    v___x_5675_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_toml___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_toml___closed__0_once),
        _init_l_Lake_Toml_toml___closed__0,
    );
    v___x_5676_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
    v___x_5677_ = l_Lean_Parser_withCache(v___x_5676_, v___x_5675_);
    return v___x_5677_;
}
pub unsafe fn _init_l_Lake_Toml_toml() -> *mut LeanObject {
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    v___x_5678_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_toml___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_toml___closed__1_once),
        _init_l_Lake_Toml_toml___closed__1,
    );
    return v___x_5678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Grammar(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Toml_ParserUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_Toml_trailingWs = _init_l_Lake_Toml_trailingWs();
    lean_mark_persistent(l_Lake_Toml_trailingWs);
    l_Lake_Toml_trailingSep = _init_l_Lake_Toml_trailingSep();
    lean_mark_persistent(l_Lake_Toml_trailingSep);
    l_Lake_Toml_unquotedKey = _init_l_Lake_Toml_unquotedKey();
    lean_mark_persistent(l_Lake_Toml_unquotedKey);
    l_Lake_Toml_basicString = _init_l_Lake_Toml_basicString();
    lean_mark_persistent(l_Lake_Toml_basicString);
    l_Lake_Toml_literalString = _init_l_Lake_Toml_literalString();
    lean_mark_persistent(l_Lake_Toml_literalString);
    l_Lake_Toml_mlBasicString = _init_l_Lake_Toml_mlBasicString();
    lean_mark_persistent(l_Lake_Toml_mlBasicString);
    l_Lake_Toml_mlLiteralString = _init_l_Lake_Toml_mlLiteralString();
    lean_mark_persistent(l_Lake_Toml_mlLiteralString);
    l_Lake_Toml_quotedKey = _init_l_Lake_Toml_quotedKey();
    lean_mark_persistent(l_Lake_Toml_quotedKey);
    l_Lake_Toml_simpleKey = _init_l_Lake_Toml_simpleKey();
    lean_mark_persistent(l_Lake_Toml_simpleKey);
    l_Lake_Toml_key = _init_l_Lake_Toml_key();
    lean_mark_persistent(l_Lake_Toml_key);
    l_Lake_Toml_stdTable = _init_l_Lake_Toml_stdTable();
    lean_mark_persistent(l_Lake_Toml_stdTable);
    l_Lake_Toml_arrayTable = _init_l_Lake_Toml_arrayTable();
    lean_mark_persistent(l_Lake_Toml_arrayTable);
    l_Lake_Toml_table = _init_l_Lake_Toml_table();
    lean_mark_persistent(l_Lake_Toml_table);
    l_Lake_Toml_header = _init_l_Lake_Toml_header();
    lean_mark_persistent(l_Lake_Toml_header);
    l_Lake_Toml_string = _init_l_Lake_Toml_string();
    lean_mark_persistent(l_Lake_Toml_string);
    l_Lake_Toml_true = _init_l_Lake_Toml_true();
    lean_mark_persistent(l_Lake_Toml_true);
    l_Lake_Toml_false = _init_l_Lake_Toml_false();
    lean_mark_persistent(l_Lake_Toml_false);
    l_Lake_Toml_boolean = _init_l_Lake_Toml_boolean();
    lean_mark_persistent(l_Lake_Toml_boolean);
    l_Lake_Toml_numeralAntiquot = _init_l_Lake_Toml_numeralAntiquot();
    lean_mark_persistent(l_Lake_Toml_numeralAntiquot);
    l_Lake_Toml_numeral = _init_l_Lake_Toml_numeral();
    lean_mark_persistent(l_Lake_Toml_numeral);
    l_Lake_Toml_float = _init_l_Lake_Toml_float();
    lean_mark_persistent(l_Lake_Toml_float);
    l_Lake_Toml_decInt = _init_l_Lake_Toml_decInt();
    lean_mark_persistent(l_Lake_Toml_decInt);
    l_Lake_Toml_binNum = _init_l_Lake_Toml_binNum();
    lean_mark_persistent(l_Lake_Toml_binNum);
    l_Lake_Toml_octNum = _init_l_Lake_Toml_octNum();
    lean_mark_persistent(l_Lake_Toml_octNum);
    l_Lake_Toml_hexNum = _init_l_Lake_Toml_hexNum();
    lean_mark_persistent(l_Lake_Toml_hexNum);
    l_Lake_Toml_dateTime = _init_l_Lake_Toml_dateTime();
    lean_mark_persistent(l_Lake_Toml_dateTime);
    l_Lake_Toml_val = _init_l_Lake_Toml_val();
    lean_mark_persistent(l_Lake_Toml_val);
    l_Lake_Toml_array = _init_l_Lake_Toml_array();
    lean_mark_persistent(l_Lake_Toml_array);
    l_Lake_Toml_inlineTable = _init_l_Lake_Toml_inlineTable();
    lean_mark_persistent(l_Lake_Toml_inlineTable);
    l_Lake_Toml_keyval = _init_l_Lake_Toml_keyval();
    lean_mark_persistent(l_Lake_Toml_keyval);
    l_Lake_Toml_expression = _init_l_Lake_Toml_expression();
    lean_mark_persistent(l_Lake_Toml_expression);
    l_Lake_Toml_key_formatter___closed__0___boxed__const__1 =
        _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1();
    lean_mark_persistent(l_Lake_Toml_key_formatter___closed__0___boxed__const__1);
    l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1();
    lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1);
    l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1 =
        _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1();
    lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1);
    l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1 =
        _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1();
    lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1);
    l_Lake_Toml_toml = _init_l_Lake_Toml_toml();
    lean_mark_persistent(l_Lake_Toml_toml);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Grammar(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Grammar(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Toml_ParserUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Formatter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Grammar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Grammar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Toml_Grammar(builtin);
}
